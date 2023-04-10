/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#[cfg(test)]
mod tests {
    use std::vec;

    use crate::{
        BasicOps, Count, CountAdd, CountSub, Key, RankTree, Splay, SplayWithKey,
    };

    #[test]
    fn luogu_1486() {
        let mut splay = RankTree::<i32>::new();
        splay.insert(60);
        splay.insert(70);
        assert_eq!(splay.size(), 2);
        assert_eq!(splay.query_kth(1), Some(&60));
        splay.insert(80);
        splay.del_smaller(&75);
        assert_eq!(splay.size(), 1);
        assert_eq!(splay.query_kth(1), Some(&80));
        assert_eq!(splay.query_kth(2), None);
    }

    #[test]
    fn luogu_1503() {
        struct SplayData {
            key: u32,
        }
        impl From<u32> for SplayData {
            fn from(key: u32) -> Self {
                Self { key }
            }
        }
        impl Key<u32> for SplayData {
            fn key(&self) -> &u32 {
                &self.key
            }
        }
        impl BasicOps for SplayData {}
        let mut destroyed = Vec::new();
        let mut splay = SplayWithKey::<u32, SplayData>::new();
        let n = 7;
        let d =
            |splay: &mut SplayWithKey<_, _>, destroyed: &mut Vec<u32>, x| {
                destroyed.push(x);
                splay.insert_owned_key(x);
            };
        let r = |splay: &mut SplayWithKey<_, _>, destroyed: &mut Vec<u32>| {
            let x = destroyed.pop().unwrap();
            splay.delete(&x);
        };
        let q = |splay: &mut SplayWithKey<u32, SplayData>, x, expected| {
            let begin = match splay.query_first_le(&x) {
                Some(d) => d.key + 1,
                None => 1,
            };
            let end = match splay.query_first_ge(&x) {
                Some(d) => d.key,
                None => n + 1,
            };
            let ans = if end <= begin { 0 } else { end - begin };
            assert_eq!(ans, expected);
        };
        d(&mut splay, &mut destroyed, 3);
        d(&mut splay, &mut destroyed, 6);
        d(&mut splay, &mut destroyed, 5);
        q(&mut splay, 4, 1);
        q(&mut splay, 5, 0);
        r(&mut splay, &mut destroyed);
        q(&mut splay, 4, 2);
        r(&mut splay, &mut destroyed);
        q(&mut splay, 4, 4);
    }

    #[test]
    fn luogu_1090() {
        struct SplayData {
            key: i32,
            cnt: u32,
        }
        impl BasicOps for SplayData {
            fn push_up(&mut self, _: Option<&Self>, _: Option<&Self>) {}
        }
        impl Key<i32> for SplayData {
            fn key(&self) -> &i32 {
                &self.key
            }
        }
        impl From<i32> for SplayData {
            fn from(key: i32) -> Self {
                SplayData { key, cnt: 1 }
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
        let mut splay = SplayWithKey::<i32, SplayData>::from(vec![1, 2, 9]);
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
            fn push_up(&mut self, _: Option<&Self>, _: Option<&Self>) {}
        }
        impl Key<i32> for SplayData {
            fn key(&self) -> &i32 {
                &self.key
            }
        }
        let mut splay = SplayWithKey::<i32, SplayData>::new();
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
        impl Key<i32> for SplayData {
            fn key(&self) -> &i32 {
                &self.key
            }
        }
        fn interval_add(
            splay: &mut SplayWithKey<i32, SplayData>,
            x: i32,
            y: i32,
            k: i32,
        ) {
            let mut interval = splay.get_closed_interval(&x, &y);
            interval.update_root_data(|d| {
                d.value += k;
                d.lazy += k;
            });
        }
        fn point_query(
            splay: &mut SplayWithKey<i32, SplayData>,
            x: i32,
        ) -> i32 {
            assert!(splay.find(&x));
            splay.root_data().unwrap().value
        }
        let mut splay = Splay::from_with_constructor(
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
        assert!(interval.collect_data().is_empty());
        let interval = splay.get_closed_interval(&0, &0);
        assert!(interval.collect_data().is_empty());
        let interval = splay.get_closed_interval(&2, &2);
        assert_eq!(
            interval
                .take_all_data()
                .iter()
                .map(|x| (x.key, x.value))
                .collect::<Vec<_>>(),
            vec![(2, 6)],
        );
        // (1, 0), (3, 12), (4, 10), (5, 9)
        assert_eq!(
            splay
                .collect_data()
                .iter()
                .map(|x| (x.key, x.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (3, 12), (4, 10), (5, 9)],
        );

        let interval = splay.get_closed_interval(&3, &4);
        assert_eq!(
            interval
                .take_all_data()
                .iter()
                .map(|x| (x.key, x.value))
                .collect::<Vec<_>>(),
            vec![(3, 12), (4, 10)],
        );
        // (1, 0), (5, 9)
        assert_eq!(
            splay
                .collect_data()
                .iter()
                .map(|x| (x.key, x.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (5, 9)],
        );

        let interval = splay.get_closed_interval(&0, &6);
        assert_eq!(
            interval
                .take_all_data()
                .iter()
                .map(|x| (x.key, x.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (5, 9)],
        );
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
        impl Key<u8> for SplayData {
            fn key(&self) -> &u8 {
                &self.key
            }
        }
        impl From<u8> for SplayData {
            fn from(key: u8) -> Self {
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
        fn num_less_than(splay: &mut SplayWithKey<u8, SplayData>, x: u8) -> u8 {
            match splay.to_interval().get_interval_lt(&x).root_data() {
                Some(d) => d.scnt,
                None => 0,
            }
        }
        let mut splay = SplayWithKey::<u8, SplayData>::new();
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
