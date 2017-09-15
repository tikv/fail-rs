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

//! A failpoints implementation for rust.

extern crate rand;

use std::str::FromStr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, RwLock, TryLockError};
use std::thread;
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
                return Err(format!("parentheses not match in {:?}", s));
            }
            args = Some(&second[..second.len() - 1]);
        }

        let mut frequency = 1f32;
        let (first, second) = partition(remain, '%');
        if let Some(second) = second {
            remain = second;
            match first.parse::<f32>() {
                Err(e) => return Err(format!("failed to parse frequency in {:?}: {}", s, e)),
                Ok(freq) => frequency = freq / 100.0,
            }
        }

        let mut max_cnt = None;
        let (first, second) = partition(remain, '*');
        if let Some(second) = second {
            remain = second;
            match first.parse() {
                Err(e) => return Err(format!("failed to parse count in {:?}: {}", s, e)),
                Ok(cnt) => max_cnt = Some(cnt),
            }
        }

        let parse_timeout = || match args {
            None => return Err("sleep require timeout".to_owned()),
            Some(timeout_str) => match timeout_str.parse() {
                Err(e) => return Err(format!("failed to parse timeout in {:?}: {}", s, e)),
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
            _ => return Err(format!("unrecognized command {:?}", s)),
        };

        Ok(Action::new(task, frequency, max_cnt))
    }
}

// A better name?
pub type ReturnValue = Option<String>;

pub trait FromReturnStr {
    fn from_return_str(from: ReturnValue) -> Self;
}

impl FromReturnStr for () {
    fn from_return_str(_: ReturnValue) -> () {}
}

pub struct FailPoint {
    name: &'static str,
    pause: Mutex<bool>,
    pause_notifier: Condvar,
    actions: RwLock<Vec<Action>>,
}

impl FailPoint {
    pub fn new(name: &'static str) -> FailPoint {
        FailPoint {
            name: name,
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

    pub fn eval(&self) -> Option<ReturnValue> {
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
                None => panic!("failpoint {} panic", self.name),
            },
            Task::Print(msg) => match msg {
                Some(ref msg) => println!("{}", msg),
                None => println!("failpoint {} executed.", self.name),
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

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::{mpsc, Arc};

    #[test]
    fn test_off() {
        let point = FailPoint::new("test_fail_point_off");
        point.set_actions(vec![Action::new(Task::Off, 1.0, None)]);
        assert!(point.eval().is_none());
    }

    #[test]
    fn test_return() {
        let point = FailPoint::new("test_fail_point_return");
        point.set_actions(vec![Action::new(Task::Return(None), 1.0, None)]);
        let res = point.eval();
        assert_eq!(res, Some(None));

        let ret = Some("test".to_owned());
        point.set_actions(vec![Action::new(Task::Return(ret.clone()), 1.0, None)]);
        let res = point.eval();
        assert_eq!(res, Some(ret));
    }

    #[test]
    fn test_sleep() {
        let point = FailPoint::new("test_fail_point_sleep");
        let timer = Instant::now();
        point.set_actions(vec![Action::new(Task::Sleep(1000), 1.0, None)]);
        assert!(point.eval().is_none());
        assert!(timer.elapsed() > Duration::from_millis(1000));
    }

    #[should_panic]
    #[test]
    fn test_panic() {
        let point = FailPoint::new("test_fail_point_panic");
        point.set_actions(vec![Action::new(Task::Panic(None), 1.0, None)]);
        point.eval();
    }

    #[test]
    fn test_print() {
        let point = FailPoint::new("test_fail_point_print");
        point.set_actions(vec![Action::new(Task::Print(None), 1.0, None)]);
        assert!(point.eval().is_none());
    }

    #[test]
    fn test_pause() {
        let point = Arc::new(FailPoint::new("test_fail_point_pause"));
        point.set_actions(vec![Action::new(Task::Pause, 1.0, None)]);
        let p = point.clone();
        let (tx, rx) = mpsc::channel();
        thread::spawn(move || {
            assert_eq!(p.eval(), None);
            tx.send(()).unwrap();
        });
        assert!(rx.recv_timeout(Duration::from_secs(1)).is_err());
        point.set_actions(vec![Action::new(Task::Off, 1.0, None)]);
        rx.recv_timeout(Duration::from_secs(1)).unwrap();
    }

    #[test]
    fn test_yield() {
        let point = FailPoint::new("test_fail_point_yield");
        point.set_actions(vec![Action::new(Task::Yield, 1.0, None)]);
        assert!(point.eval().is_none());
    }

    #[test]
    fn test_delay() {
        let point = FailPoint::new("test_fail_point_delay");
        let timer = Instant::now();
        point.set_actions(vec![Action::new(Task::Delay(1000), 1.0, None)]);
        assert!(point.eval().is_none());
        assert!(timer.elapsed() > Duration::from_millis(1000));
    }

    #[test]
    fn test_frequency_and_count() {
        let point = FailPoint::new("test_fail_point_frequency");
        point.set_actions(vec![Action::new(Task::Return(None), 0.8, Some(100))]);
        let mut count = 0;
        let mut times = 0f64;
        while count < 100 {
            if point.eval().is_some() {
                count += 1;
            }
            times += 1f64;
        }
        assert!(100.0 / 0.9 < times && times < 100.0 / 0.7, "{}", times);
        for _ in 0..times as u64 {
            assert!(point.eval().is_none());
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
}
