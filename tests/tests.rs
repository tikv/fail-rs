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

use std::sync::mpsc;
use std::time::*;
use std::*;

fn test() -> i32 {
    fail_point!("test", |s: Option<String>| s.map_or(2, |s| s.parse().unwrap()));
    0
}

// To avoid race, test them all in one function.
#[test]
fn test_macro() {
    assert_eq!(test(), 0);

    fail::cfg("tests::test", "off").unwrap();
    assert_eq!(test(), 0);

    fail::cfg("tests::test", "return(1000)").unwrap();
    assert_eq!(test(), 1000);

    let timer = Instant::now();
    fail::cfg("tests::test", "sleep(1000)").unwrap();
    assert_eq!(test(), 0);
    assert!(timer.elapsed() > Duration::from_millis(1000));

    fail::cfg("tests::test", "panic(msg)").unwrap();
    panic::catch_unwind(move || {
        test()
    }).unwrap_err();

    fail::cfg("tests::test", "print(msg)").unwrap();
    assert_eq!(test(), 0);

    fail::cfg("tests::test", "pause").unwrap();
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let val = test();
        tx.send(val).unwrap();
    });
    assert!(rx.recv_timeout(Duration::from_millis(500)).is_err());
    fail::cfg("tests::test", "off").unwrap();
    assert_eq!(rx.recv_timeout(Duration::from_millis(500)).unwrap(), 0);

    fail::cfg("tests::test", "yield").unwrap();
    assert_eq!(test(), 0);

    let timer = Instant::now();
    fail::cfg("tests::test", "delay(1000)").unwrap();
    assert_eq!(test(), 0);
    assert!(timer.elapsed() > Duration::from_millis(1000));

    fail::cfg("tests::test", "50%50*return(1)->50*return(-1)").unwrap();
    let mut sum = 0;
    for _ in 0..5000 {
        let res = test();
        assert!(res == 1 || res == -1 || res == 0);
        sum += res;
    }
    assert!(-2 < sum && sum < 2, "sum is expect between -2 and 2, but got {}", sum);
}


