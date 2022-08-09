#![feature(test)]

extern crate puyoai_core;
extern crate test;

use puyoai_core::field::BitField;
use test::Bencher;

#[bench]
fn simulate_19rensa(b: &mut Bencher) {
    let bf = BitField::from_str(concat!(
        ".G.BRG", // 13
        "GBRRYR", // 12
        "RRYYBY", // 11
        "RGYRBR", // 10
        "YGYRBY", // 9
        "YGBGYR", // 8
        "GRBGYR", // 7
        "BRBYBY", // 6
        "RYYBYY", // 5
        "BRBYBR", // 4
        "BGBYRR", // 3
        "YGBGBG", // 2
        "RBGBGG"  // 1
    ));

    b.iter(|| test::black_box(bf.clone().simulate()))
}

#[bench]
fn simulate_fast_19rensa(b: &mut Bencher) {
    let bf = BitField::from_str(concat!(
        ".G.BRG", // 13
        "GBRRYR", // 12
        "RRYYBY", // 11
        "RGYRBR", // 10
        "YGYRBY", // 9
        "YGBGYR", // 8
        "GRBGYR", // 7
        "BRBYBY", // 6
        "RYYBYY", // 5
        "BRBYBR", // 4
        "BGBYRR", // 3
        "YGBGBG", // 2
        "RBGBGG"  // 1
    ));

    b.iter(|| test::black_box(bf.clone().simulate_fast()))
}
