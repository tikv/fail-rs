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

#[macro_use]
extern crate fail;
extern crate log;

use std::sync::*;
use std::time::*;
use std::*;

use log::*;

#[test]
fn test_off() {
    let f = || {
        fail_point!("off", |_| 2);
        0
    };
    assert_eq!(f(), 0);

    fail::cfg("tests::off", "off").unwrap();
    assert_eq!(f(), 0);
}

#[test]
fn test_return() {
    let f = || {
        fail_point!("return", |s: Option<String>| {
            s.map_or(2, |s| s.parse().unwrap())
        });
        0
    };
    assert_eq!(f(), 0);

    fail::cfg("tests::return", "return(1000)").unwrap();
    assert_eq!(f(), 1000);

    fail::cfg("tests::return", "return").unwrap();
    assert_eq!(f(), 2);
}

#[test]
fn test_sleep() {
    let f = || {
        fail_point!("sleep");
    };
    let timer = Instant::now();
    f();
    assert!(timer.elapsed() < Duration::from_millis(1000));

    let timer = Instant::now();
    fail::cfg("tests::sleep", "sleep(1000)").unwrap();
    f();
    assert!(timer.elapsed() > Duration::from_millis(1000));
}

#[test]
#[should_panic]
fn test_panic() {
    let f = || {
        fail_point!("panic");
    };
    fail::cfg("tests::panic", "panic(msg)").unwrap();
    f();
}

#[test]
fn test_print() {
    struct LogCollector(Arc<Mutex<Vec<String>>>);
    impl Log for LogCollector {
        fn enabled(&self, _: &LogMetadata) -> bool {
            true
        }
        fn log(&self, record: &LogRecord) {
            let mut buf = self.0.lock().unwrap();
            buf.push(format!("{}", record.args()));
        }
    }

    let buffer = Arc::new(Mutex::new(vec![]));
    let collector = LogCollector(buffer.clone());
    log::set_logger(|e| {
        e.set(LogLevelFilter::Info);
        Box::new(collector)
    }).unwrap();

    let f = || {
        fail_point!("print");
    };
    fail::cfg("tests::print", "print(msg)").unwrap();
    f();
    let msg = buffer.lock().unwrap().pop().unwrap();
    assert_eq!(msg, "msg");

    fail::cfg("tests::print", "print").unwrap();
    f();
    let msg = buffer.lock().unwrap().pop().unwrap();
    assert_eq!(msg, "failpoint tests::print executed.");
}

#[test]
fn test_pause() {
    let f = || {
        fail_point!("pause");
    };
    f();

    fail::cfg("tests::pause", "pause").unwrap();
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        // pause
        tx.send(f()).unwrap();
        // woken up by new order pause, and then pause again.
        tx.send(f()).unwrap();
        // woken up by remove, and then quit immediately.
        tx.send(f()).unwrap();
    });

    assert!(rx.recv_timeout(Duration::from_millis(500)).is_err());
    fail::cfg("tests::pause", "pause").unwrap();
    rx.recv_timeout(Duration::from_millis(500)).unwrap();

    assert!(rx.recv_timeout(Duration::from_millis(500)).is_err());
    fail::remove("tests::pause");
    rx.recv_timeout(Duration::from_millis(500)).unwrap();

    rx.recv_timeout(Duration::from_millis(500)).unwrap();
}

#[test]
fn test_yield() {
    let f = || {
        fail_point!("yield");
    };
    fail::cfg("tests::test", "yield").unwrap();
    f();
}

#[test]
fn test_delay() {
    let f = || fail_point!("delay");
    let timer = Instant::now();
    fail::cfg("tests::delay", "delay(1000)").unwrap();
    f();
    assert!(timer.elapsed() > Duration::from_millis(1000));
}

#[test]
fn test_freq_and_count() {
    let f = || {
        fail_point!("freq_and_count", |s: Option<String>| {
            s.map_or(2, |s| s.parse().unwrap())
        });
        0
    };
    fail::cfg(
        "tests::freq_and_count",
        "50%50*return(1)->50%50*return(-1)->50*return",
    ).unwrap();
    let mut sum = 0;
    for _ in 0..5000 {
        let res = f();
        sum += res;
    }
    assert_eq!(sum, 100);
}

#[test]
fn test_condition() {
    let f = |_enabled| {
        fail_point!("condition", _enabled, |_| 2);
        0
    };
    assert_eq!(f(false), 0);

    fail::cfg("tests::condition", "return").unwrap();
    assert_eq!(f(false), 0);

    assert_eq!(f(true), 2);
}

#[test]
fn test_list() {
    fail::cfg("tests::list", "off").unwrap();
    assert!(fail::list().contains(&("tests::list".to_string(), "off".to_string())));
}
