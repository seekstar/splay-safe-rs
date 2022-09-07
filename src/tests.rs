#[cfg(test)]
mod tests {
    use std::vec;

    use crate::{BasicOps, Count, CountAdd, CountSub, Splay, WithKey};

    #[test]
    fn luogu_1090() {
        struct SplayData {
            key: i32,
            cnt: u32,
        }
        impl BasicOps for SplayData {
            type KeyType = i32;
            fn key(&self) -> &Self::KeyType {
                &self.key
            }
            fn push_up(&mut self, _: Option<&Self>, _: Option<&Self>) {}
        }
        impl WithKey for SplayData {
            fn with_key(key: Self::KeyType) -> Self {
                SplayData { key: key, cnt: 1 }
            }
        }
        impl Count for SplayData {
            type CountType = u32;
            fn cnt(&self) -> &Self::CountType {
                &self.cnt
            }
        }
        impl CountAdd for SplayData {
            fn cnt_add(&mut self, delta: &Self::CountType) {
                self.cnt += delta;
            }
        }
        impl CountSub for SplayData {
            fn cnt_sub(&mut self, delta: &Self::CountType) {
                self.cnt -= delta;
            }
        }
        let mut splay = Splay::<SplayData>::from(vec![1, 2, 9]);
        assert_eq!(splay.query_smallest().unwrap().key(), &1);
        assert!(splay.deref_root());
        assert_eq!(splay.query_smallest().unwrap().key(), &2);
        assert!(splay.deref_root());
        splay.insert_owned_key_or_inc_cnt(3);
        assert_eq!(splay.query_smallest().unwrap().key(), &3);
        assert!(splay.deref_root());
        assert_eq!(splay.query_smallest().unwrap().key(), &9);
        assert!(splay.deref_root());
        splay.insert_owned_key_or_inc_cnt(12);
        assert_eq!(splay.query_smallest().unwrap().key(), &12);
        assert!(splay.deref_root());
        assert!(splay.query_smallest().is_none());
    }

    #[test]
    fn luogu_2073() {
        #[derive(PartialEq, Debug)]
        struct SplayData {
            key: i32,
            value: i32,
        }
        impl BasicOps for SplayData {
            type KeyType = i32;
            fn key(&self) -> &Self::KeyType {
                &self.key
            }
            fn push_up(&mut self, _: Option<&Self>, _: Option<&Self>) {}
        }
        let mut splay = Splay::new();
        assert!(splay
            .insert_owned_key_with_func(1, |key| SplayData { key, value: 1 }));
        assert!(splay
            .insert_owned_key_with_func(5, |key| SplayData { key, value: 2 }));
        assert_eq!(splay.pop_largest(), Some(SplayData { key: 5, value: 2 }));
        assert!(splay
            .insert_owned_key_with_func(3, |key| SplayData { key, value: 3 }));
        assert_eq!(splay.pop_smallest(), Some(SplayData { key: 1, value: 1 }));
        assert!(splay
            .insert_owned_key_with_func(2, |key| SplayData { key, value: 5 }));
        assert_eq!(
            splay.collect_data(),
            vec![
                &SplayData { key: 2, value: 5 },
                &SplayData { key: 3, value: 3 },
            ]
        );
        assert_eq!(
            splay.take_all_data(),
            vec![
                SplayData { key: 2, value: 5 },
                SplayData { key: 3, value: 3 },
            ]
        );
    }

    #[test]
    fn luogu_3368() {
        struct SplayData {
            key: i32,
            value: i32,
            lazy: i32,
        }
        impl BasicOps for SplayData {
            type KeyType = i32;
            fn key(&self) -> &Self::KeyType {
                &self.key
            }
            fn push_down(
                &mut self,
                lc: Option<&mut Self>,
                rc: Option<&mut Self>,
            ) {
                if self.lazy != 0 {
                    if let Some(c) = lc {
                        c.value += self.lazy;
                        c.lazy += self.lazy;
                    }
                    if let Some(c) = rc {
                        c.value += self.lazy;
                        c.lazy += self.lazy;
                    }
                    self.lazy = 0;
                }
            }
        }
        fn interval_add(splay: &mut Splay<SplayData>, x: i32, y: i32, k: i32) {
            let mut interval = splay.get_closed_interval(&x, &y);
            interval.update_root_data(|d| {
                d.value += k;
                d.lazy += k;
            });
        }
        fn point_query(splay: &mut Splay<SplayData>, x: i32) -> i32 {
            assert!(splay.find(&x));
            splay.root_data().unwrap().value
        }
        let mut splay = Splay::from_sorted(
            vec![(1, 1), (2, 5), (3, 4), (4, 2), (5, 3)],
            |(key, value)| SplayData {
                key,
                value,
                lazy: 0,
            },
        );
        // 1, 5, 4, 2, 3
        interval_add(&mut splay, 2, 4, 2);
        // 1, 7, 6, 4, 3
        assert_eq!(point_query(&mut splay, 3), 6);
        interval_add(&mut splay, 1, 5, -1);
        // 0, 6, 5, 3, 2
        interval_add(&mut splay, 3, 5, 7);
        // 0, 6, 12, 10, 9
        assert_eq!(point_query(&mut splay, 4), 10);

        // Additional
        let interval = splay.get_closed_interval(&6, &6);
        assert!(interval.root_data().is_none());
        let interval = splay.get_closed_interval(&0, &0);
        assert!(interval.root_data().is_none());
        let mut interval = splay.get_closed_interval(&2, &2);
        interval.delete();
        // (1, 0), (3, 12), (4, 10), (5, 9)
        assert_eq!(
            splay
                .collect_data()
                .iter()
                .map(|x| (x.key, x.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (3, 12), (4, 10), (5, 9)],
        );
        let mut interval = splay.get_closed_interval(&3, &4);
        interval.delete();
        // (1, 0), (5, 9)
        assert_eq!(
            splay
                .collect_data()
                .iter()
                .map(|x| (x.key, x.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (5, 9)],
        );
        let mut interval = splay.get_closed_interval(&0, &6);
        interval.delete();
        assert!(splay.collect_data().is_empty());
    }

    #[test]
    fn luogu_1428() {
        struct SplayData {
            key: u8,
            cnt: u8,
            scnt: u8,
        }
        impl BasicOps for SplayData {
            type KeyType = u8;
            fn key(&self) -> &Self::KeyType {
                &self.key
            }
            fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>) {
                self.scnt = self.cnt;
                if let Some(c) = lc {
                    self.scnt += c.scnt;
                }
                if let Some(c) = rc {
                    self.scnt += c.scnt;
                }
            }
        }
        impl WithKey for SplayData {
            fn with_key(key: Self::KeyType) -> Self {
                SplayData {
                    key,
                    cnt: 1,
                    scnt: 1,
                }
            }
        }
        impl Count for SplayData {
            type CountType = u8;
            fn cnt(&self) -> &Self::CountType {
                &self.cnt
            }
        }
        impl CountAdd for SplayData {
            fn cnt_add(&mut self, delta: &Self::CountType) {
                self.cnt += delta;
            }
        }
        fn num_less_than(splay: &mut Splay<SplayData>, x: u8) -> u8 {
            match splay.to_interval().get_interval_lt(&x).root_data() {
                Some(d) => d.scnt,
                None => 0,
            }
        }
        let mut splay = Splay::<SplayData>::new();
        assert_eq!(num_less_than(&mut splay, 4), 0);
        splay.insert_owned_key_or_inc_cnt(4);
        assert_eq!(num_less_than(&mut splay, 3), 0);
        splay.insert_owned_key_or_inc_cnt(3);
        assert_eq!(num_less_than(&mut splay, 0), 0);
        splay.insert_owned_key_or_inc_cnt(0);
        assert_eq!(num_less_than(&mut splay, 5), 3);
        splay.insert_owned_key_or_inc_cnt(5);
        assert_eq!(num_less_than(&mut splay, 1), 1);
        splay.insert_owned_key_or_inc_cnt(1);
        assert_eq!(num_less_than(&mut splay, 2), 2);
        splay.insert_owned_key_or_inc_cnt(2);
    }
}
