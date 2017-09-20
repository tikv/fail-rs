// Copyright 2017 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

//! A fail point implementation for rust.
//!
//! Fail points are code points that are used to inject errors by users at runtime.
//! This crate is inspired by FreeBSD's [failpoints](https://freebsd.org/cgi/man.cgi?query=fail).
//! Unlike FreeBSD's implementation, this crate only supports the configuration from
//! environment variables and API.
//!
//! ## Installation
//!
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! fail = "0.1"
//! ```
//!
//! ## Example
//!
//! ```rust
//! #[macro_use]
//! extern crate fail;
//!
//! fn f1() {
//!     fail_point!("example");
//!     panic!();
//! }
//!
//! fn main() {
//!    fail::setup();
//!    fail::cfg("rust_out::example", "return").unwrap();
//!    f1();
//!    fail::teardown();
//! }
//! ```
//!
//! The above example defines a fail point named "example" and then configures it as `return`.
//! So the `f1` function will return early and never panic. You can also configure it via the
//! `FAILPOINTS=rust_out::example=return` environment variable. For more supported
//! configuration, see docs for macro [`fail_point`](macro.fail_point.html)
//! and [`setup`](fn.setup.html).
//!
//! If you want to disable all the fail points at compile time, you can enable features `disabled`.
#![deny(missing_docs, missing_debug_implementations)]

#[macro_use]
extern crate lazy_static;
extern crate rand;

use std::collections::HashMap;
use std::env::VarError;
use std::str::FromStr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock, TryLockError};
use std::{env, thread};
use std::time::{Duration, Instant};

use rand::Closed01;

/// Supported tasks.
#[derive(Clone, Debug, PartialEq)]
enum Task {
    /// Do nothing.
    Off,
    /// Return the value.
    Return(Option<String>),
    /// Sleep for some milliseconds.
    Sleep(u64),
    /// Panic with the message.
    Panic(Option<String>),
    /// Print the message.
    Print(Option<String>),
    /// Sleep until other action is set.
    Pause,
    /// Yield the CPU.
    Yield,
    /// Busy waiting for some milliseconds.
    Delay(u64),
}

#[derive(Debug)]
struct Action {
    task: Task,
    freq: f32,
    count: Option<AtomicUsize>,
}

impl PartialEq for Action {
    fn eq(&self, hs: &Action) -> bool {
        if self.task != hs.task || self.freq != hs.freq {
            return false;
        }
        if let Some(ref lhs) = self.count {
            if let Some(ref rhs) = hs.count {
                return lhs.load(Ordering::Relaxed) == rhs.load(Ordering::Relaxed);
            }
        } else if hs.count.is_none() {
            return true;
        }
        false
    }
}

impl Action {
    fn new(task: Task, freq: f32, max_cnt: Option<usize>) -> Action {
        Action {
            task: task,
            freq: freq,
            count: max_cnt.map(AtomicUsize::new),
        }
    }

    fn get_task(&self) -> Option<Task> {
        if let Some(ref cnt) = self.count {
            let c = cnt.load(Ordering::Acquire);
            if c == 0 {
                return None;
            }
        }
        if self.freq < 1f32 {
            let Closed01(f) = rand::random::<Closed01<f32>>();
            if f > self.freq {
                return None;
            }
        }
        if let Some(ref cnt) = self.count {
            loop {
                let c = cnt.load(Ordering::Acquire);
                if c == 0 {
                    return None;
                }
                if c == cnt.compare_and_swap(c, c - 1, Ordering::AcqRel) {
                    break;
                }
            }
        }
        Some(self.task.clone())
    }
}

fn partition(s: &str, pattern: char) -> (&str, Option<&str>) {
    let mut splits = s.splitn(2, pattern);
    (splits.next().unwrap(), splits.next())
}

impl FromStr for Action {
    type Err = String;

    /// Parse an action.
    ///
    /// `s` should be in the format `[p%][cnt*]task[(args)]`, `p%` is the frequency,
    /// `cnt` is the max times the action can be triggered.
    fn from_str(s: &str) -> Result<Action, String> {
        let mut remain = s.trim();
        let mut args = None;
        // in case there is '%' in args, we need to parse it first.
        let (first, second) = partition(remain, '(');
        if let Some(second) = second {
            remain = first;
            if !second.ends_with(")") {
                return Err("parentheses not match".to_owned());
            }
            args = Some(&second[..second.len() - 1]);
        }

        let mut frequency = 1f32;
        let (first, second) = partition(remain, '%');
        if let Some(second) = second {
            remain = second;
            match first.parse::<f32>() {
                Err(e) => return Err(format!("failed to parse frequency: {}", e)),
                Ok(freq) => frequency = freq / 100.0,
            }
        }

        let mut max_cnt = None;
        let (first, second) = partition(remain, '*');
        if let Some(second) = second {
            remain = second;
            match first.parse() {
                Err(e) => return Err(format!("failed to parse count: {}", e)),
                Ok(cnt) => max_cnt = Some(cnt),
            }
        }

        let parse_timeout = || match args {
            None => return Err("sleep require timeout".to_owned()),
            Some(timeout_str) => match timeout_str.parse() {
                Err(e) => return Err(format!("failed to parse timeout: {}", e)),
                Ok(timeout) => Ok(timeout),
            },
        };

        let task = match remain {
            "off" => Task::Off,
            "return" => Task::Return(args.map(str::to_owned)),
            "sleep" => Task::Sleep(try!(parse_timeout())),
            "panic" => Task::Panic(args.map(str::to_owned)),
            "print" => Task::Print(args.map(str::to_owned)),
            "pause" => Task::Pause,
            "yield" => Task::Yield,
            "delay" => Task::Delay(try!(parse_timeout())),
            _ => return Err(format!("unrecognized command {:?}", remain)),
        };

        Ok(Action::new(task, frequency, max_cnt))
    }
}

struct FailPoint {
    pause: Mutex<bool>,
    pause_notifier: Condvar,
    actions: RwLock<Vec<Action>>,
}

impl FailPoint {
    fn new() -> FailPoint {
        FailPoint {
            pause: Mutex::new(false),
            pause_notifier: Condvar::new(),
            actions: RwLock::new(vec![]),
        }
    }

    #[allow(dead_code)]
    fn set_actions(&self, actions: Vec<Action>) {
        loop {
            // TODO: maybe busy waiting here.
            match self.actions.try_write() {
                Err(TryLockError::WouldBlock) => {}
                Ok(mut guard) => {
                    *guard = actions;
                    return;
                }
                Err(e) => panic!("unexpected poison: {:?}", e),
            }

            let mut guard = self.pause.lock().unwrap();
            *guard = false;
            self.pause_notifier.notify_all();
        }
    }

    fn eval(&self, name: &str) -> Option<Option<String>> {
        let task = {
            let actions = self.actions.read().unwrap();
            match actions.iter().filter_map(|a| a.get_task()).next() {
                Some(Task::Pause) => {
                    let mut guard = self.pause.lock().unwrap();
                    *guard = true;
                    loop {
                        guard = self.pause_notifier.wait(guard).unwrap();
                        if !*guard {
                            break;
                        }
                    }
                    return None;
                }
                Some(t) => t,
                None => return None,
            }
        };

        match task {
            Task::Off => {}
            Task::Return(s) => return Some(s),
            Task::Sleep(t) => thread::sleep(Duration::from_millis(t)),
            Task::Panic(msg) => match msg {
                Some(ref msg) => panic!("{}", msg),
                None => panic!("failpoint {} panic", name),
            },
            Task::Print(msg) => match msg {
                Some(ref msg) => println!("{}", msg),
                None => println!("failpoint {} executed.", name),
            },
            Task::Pause => unreachable!(),
            Task::Yield => thread::yield_now(),
            Task::Delay(t) => {
                let timer = Instant::now();
                let timeout = Duration::from_millis(t);
                while timer.elapsed() < timeout {}
            }
        }
        None
    }
}

#[derive(Default)]
struct FailPointRegistry {
    // TODO: remove rwlock or store *mut FailPoint
    registry: RwLock<HashMap<String, Arc<FailPoint>>>,
}

lazy_static! {
    static ref REGISTRY: FailPointRegistry = FailPointRegistry::default();
}

/// Set up the fail point system.
///
/// The `FAILPOINTS` environment variable is used to configure all the fail points.
/// The format of `FAILPOINTS` is `full_path_to_failpoint=actions;...`.
///
/// `full_path_to_failpoint` is the full module path to the fail point and its name.
/// For more information, see macro [`fail_point`](macro.fail_point.html) and
/// [`cfg`](fn.cfg.html).
pub fn setup() {
    let mut registry = REGISTRY.registry.write().unwrap();
    let failpoints = match env::var("FAILPOINTS") {
        Ok(s) => s,
        Err(VarError::NotPresent) => return,
        Err(e) => panic!("invalid failpoints: {:?}", e),
    };
    for mut cfg in failpoints.trim().split(";") {
        cfg = cfg.trim();
        if cfg.trim().is_empty() {
            continue;
        }
        let (name, order) = partition(cfg, '=');
        match order {
            None => panic!("invalid failpoint: {:?}", cfg),
            Some(order) => set(&mut registry, name.to_owned(), order).unwrap(),
        }
    }
}

/// Tear down the fail point system.
///
/// All the paused fail points will be notified before they are deactivated.
pub fn teardown() {
    let mut registry = REGISTRY.registry.write().unwrap();
    for (_, p) in &*registry {
        // wake up all pause failpoint.
        p.set_actions(vec![]);
    }
    registry.clear();
}

#[doc(hidden)]
pub fn eval<R, F: FnOnce(Option<String>) -> R>(name: &str, f: F) -> Option<R> {
    let p = {
        let registry = REGISTRY.registry.read().unwrap();
        match registry.get(name) {
            None => return None,
            Some(p) => p.clone(),
        }
    };
    p.eval(name).map(f)
}

/// Set new actions to a fail point at runtime.
///
/// The format of actions is `action[->action...]`. When multiple actions are specified,
/// an action will be checked only when its former action is not triggered.
///
/// The format of an action is `[p%][cnt*]task[(arg)]`. `p%` is the expected probability that
/// the action is triggered, and `cnt*` is the max times the action can be triggered.
/// Supported `task` includes:
///
/// - `off`, the fail point will do nothing.
/// - `return(arg)`, return early when the fail point is triggered. `arg` is passed to `$e` (
/// defined via the `fail_point!` macro) as a string.
/// - `sleep(milliseconds)`, sleep for the specified time.
/// - `panic(msg)`, panic with the message.
/// - `print(msg)`, print the message.
/// - `pause`, sleep until other action is set to the fail point.
/// - `yield`, yield the CPU.
/// - `delay(milliseconds)`, busy waiting for the specified time.
///
/// For example, `20%3*print(still alive!)->panic` means the fail point has 20% chance to print a
/// message "still alive!" and 80% chance to panic. And the message will be printed at most 3
/// times.
pub fn cfg<S: Into<String>>(name: S, actions: &str) -> Result<(), String> {
    let mut registry = REGISTRY.registry.write().unwrap();
    set(&mut registry, name.into(), actions)
}

/// Remove a fail point.
///
/// If the fail point doesn't exist, nothing will happen.
pub fn remove<S: AsRef<str>>(name: S) {
    let mut registry = REGISTRY.registry.write().unwrap();
    if let Some(p) = registry.remove(name.as_ref()) {
        // wake up all pause failpoint.
        p.set_actions(vec![]);
    }
}

fn set(
    registry: &mut HashMap<String, Arc<FailPoint>>,
    name: String,
    actions: &str,
) -> Result<(), String> {
    // `actions` are in the format of `failpoint[->failpoint...]`.
    let actions = try!(actions.split("->").map(Action::from_str).collect());
    // Please note that we can't figure out whether there is a failpoint named `name`,
    // so we may insert a failpoint that doesn't exist at all.
    let p = registry
        .entry(name)
        .or_insert_with(|| Arc::new(FailPoint::new()));
    p.set_actions(actions);
    Ok(())
}

/// The only entry to define a fail point.
///
/// When a fail point is defined, it's referenced via the full module path and name in the
/// format of `crate::module::submodule::fail_point_name`. For example, library A defines
/// a fail point in lib.rs as follows:
///
/// ```rust
/// pub fn f() {
///     fail_point!("p1");
/// }
///
/// mod M {
///     fn f() {
///         fail_point!("p2");
///     }
/// }
/// ```
/// The full name of the `p1` fail point is `A::p1`, and `p2` is `A::M::p2`.
///
/// `$e` is used to transform a string to the return type of outer function or closure. If
/// the return type is `()`, then you can use the `fail_point!($name)` shortcut.
///
/// If you provide an additional condition `$cond`, then the condition will be evaluated
/// before the fail point is actually checked.
#[macro_export]
macro_rules! fail_point {
    ($name:expr, $e:expr) => {{
        let name = concat!(module_path!(), "::", $name);
        if let Some(res) = $crate::eval(name, $e) {
            return res;
        }
    }};
    ($name:expr) => {{
        fail_point!($name, |_| {});
    }};
    ($name:expr, $cond:expr, $e:expr) => {{
        if $cond {
            fail_point!($name, $e);
        }
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::{mpsc, Arc};

    #[test]
    fn test_off() {
        let point = FailPoint::new();
        point.set_actions(vec![Action::new(Task::Off, 1.0, None)]);
        assert!(point.eval("test_fail_point_off").is_none());
    }

    #[test]
    fn test_return() {
        let point = FailPoint::new();
        point.set_actions(vec![Action::new(Task::Return(None), 1.0, None)]);
        let res = point.eval("test_fail_point_return");
        assert_eq!(res, Some(None));

        let ret = Some("test".to_owned());
        point.set_actions(vec![Action::new(Task::Return(ret.clone()), 1.0, None)]);
        let res = point.eval("test_fail_point_return");
        assert_eq!(res, Some(ret));
    }

    #[test]
    fn test_sleep() {
        let point = FailPoint::new();
        let timer = Instant::now();
        point.set_actions(vec![Action::new(Task::Sleep(1000), 1.0, None)]);
        assert!(point.eval("test_fail_point_sleep").is_none());
        assert!(timer.elapsed() > Duration::from_millis(1000));
    }

    #[should_panic]
    #[test]
    fn test_panic() {
        let point = FailPoint::new();
        point.set_actions(vec![Action::new(Task::Panic(None), 1.0, None)]);
        point.eval("test_fail_point_panic");
    }

    #[test]
    fn test_print() {
        let point = FailPoint::new();
        point.set_actions(vec![Action::new(Task::Print(None), 1.0, None)]);
        assert!(point.eval("test_fail_point_print").is_none());
    }

    #[test]
    fn test_pause() {
        let point = Arc::new(FailPoint::new());
        point.set_actions(vec![Action::new(Task::Pause, 1.0, None)]);
        let p = point.clone();
        let (tx, rx) = mpsc::channel();
        thread::spawn(move || {
            assert_eq!(p.eval("test_fail_point_pause"), None);
            tx.send(()).unwrap();
        });
        assert!(rx.recv_timeout(Duration::from_secs(1)).is_err());
        point.set_actions(vec![Action::new(Task::Off, 1.0, None)]);
        rx.recv_timeout(Duration::from_secs(1)).unwrap();
    }

    #[test]
    fn test_yield() {
        let point = FailPoint::new();
        point.set_actions(vec![Action::new(Task::Yield, 1.0, None)]);
        assert!(point.eval("test_fail_point_yield").is_none());
    }

    #[test]
    fn test_delay() {
        let point = FailPoint::new();
        let timer = Instant::now();
        point.set_actions(vec![Action::new(Task::Delay(1000), 1.0, None)]);
        assert!(point.eval("test_fail_point_delay").is_none());
        assert!(timer.elapsed() > Duration::from_millis(1000));
    }

    #[test]
    fn test_frequency_and_count() {
        let point = FailPoint::new();
        point.set_actions(vec![Action::new(Task::Return(None), 0.8, Some(100))]);
        let mut count = 0;
        let mut times = 0f64;
        while count < 100 {
            if point.eval("test_fail_point_frequency").is_some() {
                count += 1;
            }
            times += 1f64;
        }
        assert!(100.0 / 0.9 < times && times < 100.0 / 0.7, "{}", times);
        for _ in 0..times as u64 {
            assert!(point.eval("test_fail_point_frequency").is_none());
        }
    }

    #[test]
    fn test_parse() {
        let cases = vec![
            ("return", Action::new(Task::Return(None), 1.0, None)),
            (
                "return(64)",
                Action::new(Task::Return(Some("64".to_owned())), 1.0, None),
            ),
            ("5*return", Action::new(Task::Return(None), 1.0, Some(5))),
            ("25%return", Action::new(Task::Return(None), 0.25, None)),
            (
                "125%2*return",
                Action::new(Task::Return(None), 1.25, Some(2)),
            ),
            (
                "return(2%5)",
                Action::new(Task::Return(Some("2%5".to_owned())), 1.0, None),
            ),
            ("125%2*off", Action::new(Task::Off, 1.25, Some(2))),
            (
                "125%2*sleep(100)",
                Action::new(Task::Sleep(100), 1.25, Some(2)),
            ),
            (" 125%2*off ", Action::new(Task::Off, 1.25, Some(2))),
            ("125%2*panic", Action::new(Task::Panic(None), 1.25, Some(2))),
            (
                "125%2*panic(msg)",
                Action::new(Task::Panic(Some("msg".to_owned())), 1.25, Some(2)),
            ),
            ("125%2*print", Action::new(Task::Print(None), 1.25, Some(2))),
            (
                "125%2*print(msg)",
                Action::new(Task::Print(Some("msg".to_owned())), 1.25, Some(2)),
            ),
            ("125%2*pause", Action::new(Task::Pause, 1.25, Some(2))),
            ("125%2*yield", Action::new(Task::Yield, 1.25, Some(2))),
            ("125%2*delay(2)", Action::new(Task::Delay(2), 1.25, Some(2))),
        ];
        for (expr, exp) in cases {
            let res: Action = expr.parse().unwrap();
            assert_eq!(res, exp);
        }

        let fail_cases = vec![
            "delay",
            "sleep",
            "Return",
            "ab%return",
            "ab*return",
            "return(msg",
            "unknown",
        ];
        for case in fail_cases {
            assert!(case.parse::<Action>().is_err());
        }
    }

    // This case should be tested as integration case, but when calling `teardown` other cases
    // like `test_pause` maybe also affected, so it's better keep it here.
    #[test]
    fn test_setup_and_teardown() {
        let f1 = || {
            fail_point!("setup_and_teardown1", |_| 1);
            0
        };
        let f2 = || {
            fail_point!("setup_and_teardown2", |_| 2);
            0
        };
        env::set_var(
            "FAILPOINTS",
            "fail::tests::setup_and_teardown1=return;fail::tests::setup_and_teardown2=pause;",
        );
        setup();
        assert_eq!(f1(), 1);

        let (tx, rx) = mpsc::channel();
        thread::spawn(move || { tx.send(f2()).unwrap(); });
        assert!(rx.recv_timeout(Duration::from_millis(500)).is_err());

        teardown();
        assert_eq!(rx.recv_timeout(Duration::from_millis(500)).unwrap(), 0);
        assert_eq!(f1(), 0);
    }
}
