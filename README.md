# splay-safe-rs

## Description

Splay implemented with safe rust.

## Get started

```rs
use splay_safe_rs::{BasicOpsWithKey, KeyValue, SplayWithKey};

use std::ops::Bound;

struct SplayValue {
    vlen: usize,
    kvsize: usize,
}
impl BasicOpsWithKey<String> for SplayValue {
    fn push_up(
        &mut self,
        key: &String,
        lc: Option<&KeyValue<String, Self>>,
        rc: Option<&KeyValue<String, Self>>,
    ) {
        self.kvsize = key.len() + self.vlen;
        if let Some(d) = lc {
            self.kvsize += d.value.kvsize;
        }
        if let Some(d) = rc {
            self.kvsize += d.value.kvsize;
        }
    }
}

fn main() {
    let mut keys = SplayWithKey::<String, SplayValue>::new();
    keys.insert("aa".to_owned(), SplayValue { vlen: 1, kvsize: 3 });
    keys.insert("bb".to_owned(), SplayValue { vlen: 2, kvsize: 4 });
    keys.insert("cc".to_owned(), SplayValue { vlen: 3, kvsize: 5 });
    keys.insert("dd".to_owned(), SplayValue { vlen: 4, kvsize: 6 });
    assert_eq!(
        keys.range::<str, _>((Bound::Included("bb"), Bound::Included("cc")))
            .root_data()
            .unwrap()
            .value
            .kvsize,
        9
    );
}
```

## LICENSE

This software is licensed under Mozilla Public License Version 2.0.
