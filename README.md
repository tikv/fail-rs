# fail-rs

A fail points implementation for rust.

## Usage

First, add this to your `Cargo.toml`:

```toml
[dependencies]
fail = "0.1"
```

Next, add this to your crate:

```rust
#[macro_use]
extern crate fail;
```

Define fail points:

```
fn function_return_tuple() {
    fail_point!("name1");
}

fn function_return_others() -> u64 {
    fail_point!("name2", |r| r.map_or(2, |e| e.parse().unwrap()));
    0
}

fn function_conditional(enable: bool) {
    fail_point!("name3", enable, |_| {});
}
```

Trigger a fail point via environment variable:

```
$ FAILPOINTS=bar::foo=panic cargo run
```

In unit tests:

```
#[test]
fn test_foo() {
    fail::cfg("bar::foo", "panic");
    foo();
}
```

Triggered via HTTP API is planned but not implemented yet.
