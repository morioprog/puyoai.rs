use color::{Color, PuyoColor};
use field::{self, FieldIsEmpty, PuyoPlainField};
use field_bit::FieldBit;
use std::{self, mem};

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;
use std::simd::*;

#[cfg(all(target_feature = "avx2", target_feature = "bmi2"))]
use field_bit_256::FieldBit256;
#[cfg(all(target_feature = "avx2", target_feature = "bmi2"))]
use frame;
#[cfg(all(target_feature = "avx2", target_feature = "bmi2"))]
use rensa_result::RensaResult;
#[cfg(all(target_feature = "avx2", target_feature = "bmi2"))]
use rensa_tracker::{RensaNonTracker, RensaTracker};
#[cfg(all(target_feature = "avx2", target_feature = "bmi2"))]
use score;
#[cfg(all(target_feature = "avx2", target_feature = "bmi2"))]
use sseext;

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct BitField {
    m: [FieldBit; 3],
}

impl BitField {
    pub fn new() -> BitField {
        BitField {
            m: unsafe {
                [
                    FieldBit::empty(),
                    FieldBit::from_values(
                        0xFFFF, 0x8001, 0x8001, 0x8001, 0x8001, 0x8001, 0x8001, 0xFFFF,
                    ),
                    FieldBit::empty(),
                ]
            },
        }
    }

    pub unsafe fn uninitialized() -> BitField {
        BitField {
            m: [
                FieldBit::uninitialized(),
                FieldBit::uninitialized(),
                FieldBit::uninitialized(),
            ],
        }
    }

    pub fn from_plain_field(pf: PuyoPlainField) -> BitField {
        let mut bf = BitField::new();

        // TODO(mayah): We have better algorithm here.
        for x in 0..field::MAP_WIDTH {
            for y in 0..field::MAP_HEIGHT {
                bf.set_color(x, y, pf.color(x, y))
            }
        }

        bf
    }

    pub fn from_str(s: &str) -> BitField {
        BitField::from_plain_field(PuyoPlainField::from_str(s))
    }

    pub fn color(&self, x: usize, y: usize) -> PuyoColor {
        let b0: u8 = if unsafe { self.m[0].get(x, y) } { 1 } else { 0 };
        let b1: u8 = if unsafe { self.m[1].get(x, y) } { 2 } else { 0 };
        let b2: u8 = if unsafe { self.m[2].get(x, y) } { 4 } else { 0 };

        unsafe { mem::transmute(b0 | b1 | b2) }
    }

    pub fn is_color(&self, x: usize, y: usize, c: PuyoColor) -> bool {
        unsafe { self.bits(c).get(x, y) }
    }

    pub fn is_empty(&self, x: usize, y: usize) -> bool {
        let whole = self.m[0] | self.m[1] | self.m[2];
        return !unsafe { whole.get(x, y) };
    }

    pub fn is_normal_color(&self, x: usize, y: usize) -> bool {
        unsafe { self.m[2].get(x, y) }
    }

    pub fn set_color(&mut self, x: usize, y: usize, c: PuyoColor) {
        let cc = c as u8;
        for i in 0..3 {
            if (cc & (1 << i)) != 0 {
                unsafe { self.m[i as usize].set(x, y) };
            } else {
                unsafe { self.m[i as usize].unset(x, y) };
            }
        }
    }

    /// Returns true if ZENKESHI.
    pub fn is_all_cleared(&self) -> bool {
        unsafe {
            (self.m[0] | self.m[1] | self.m[2])
                .masked_field_13()
                .is_empty()
        }
    }

    pub fn count_connected(&self, x: usize, y: usize) -> usize {
        if y > field::HEIGHT {
            return 0;
        }

        let c = self.color(x, y);
        let color_bits = unsafe { self.bits(c).masked_field_12() };
        unsafe { FieldBit::from_onebit(x, y).expand(&color_bits).popcount() }
    }

    pub fn count_connected_max4(&self, x: usize, y: usize) -> usize {
        if y > field::HEIGHT {
            return 0;
        }

        let c = self.color(x, y);
        let color_bits = unsafe { self.bits(c).masked_field_12() };

        unsafe {
            FieldBit::from_onebit(x, y)
                .expand1(color_bits)
                .expand1(color_bits)
                .expand1(color_bits)
                .popcount()
        }
    }

    pub fn count_connected_max4_with_color(&self, x: usize, y: usize, c: PuyoColor) -> usize {
        if y > field::HEIGHT {
            return 0;
        }

        let color_bits = unsafe { self.bits(c).masked_field_12() };

        unsafe {
            FieldBit::from_onebit(x, y)
                .expand1(color_bits)
                .expand1(color_bits)
                .expand1(color_bits)
                .popcount()
        }
    }

    /// Returns FieldBit where normal color bit is set.
    pub fn normal_color_bits(&self) -> FieldBit {
        self.m[2]
    }

    pub unsafe fn bits(&self, c: PuyoColor) -> FieldBit {
        let r0 = self.m[0].as_m128i();
        let r1 = self.m[1].as_m128i();
        let r2 = self.m[2].as_m128i();

        let v = match c {
            PuyoColor::EMPTY => {
                // 0
                let x = _mm_or_si128(_mm_or_si128(r0, r1), r2);
                _mm_xor_si128(x, _mm_setr_epi32(!0, !0, !0, !0))
            }
            PuyoColor::OJAMA => {
                // 1
                _mm_andnot_si128(r2, _mm_andnot_si128(r1, r0))
            }
            PuyoColor::WALL => {
                // 2
                _mm_andnot_si128(r2, _mm_andnot_si128(r0, r1))
            }
            PuyoColor::IRON => {
                // 3
                _mm_andnot_si128(r2, _mm_and_si128(r0, r1))
            }
            PuyoColor::RED => {
                // 4
                _mm_andnot_si128(r0, _mm_andnot_si128(r1, r2))
            }
            PuyoColor::BLUE => {
                // 5
                _mm_and_si128(r0, _mm_andnot_si128(r1, r2))
            }
            PuyoColor::YELLOW => {
                // 6
                _mm_andnot_si128(r0, _mm_and_si128(r1, r2))
            }
            PuyoColor::GREEN => {
                // 7
                _mm_and_si128(r0, _mm_and_si128(r1, r2))
            }
        };

        FieldBit::new(v)
    }

    pub fn is_connected(&self, x: usize, y: usize) -> bool {
        self.is_connected_with_color(x, y, self.color(x, y))
    }

    pub fn is_connected_with_color(&self, x: usize, y: usize, c: PuyoColor) -> bool {
        if y > field::HEIGHT {
            return false;
        }

        let color_bits = unsafe { self.bits(c).masked_field_12() };
        let single = FieldBit::from_onebit(x, y);
        !unsafe {
            single
                .expand_edge()
                .mask(color_bits)
                .not_mask(single)
                .is_empty()
        }
    }

    pub fn escape_invisible(&mut self) -> BitField {
        let mut escaped = unsafe { BitField::uninitialized() };
        for i in 0..3 {
            escaped.m[i] = unsafe { self.m[i].not_masked_field_13() };
            self.m[i] = unsafe { self.m[i].masked_field_13() };
        }

        escaped
    }

    pub fn recover_invisible(&mut self, bf: &BitField) {
        for i in 0..3 {
            unsafe { self.m[i].set_all(bf.m[i]) };
        }
    }

    pub fn calculate_height(&self) -> [i16; 8] {
        let whole = unsafe { (self.m[0] | self.m[1] | self.m[2]).masked_field_13() };
        let count = unsafe { sseext::mm_popcnt_epi16(whole.as_m128i()) };

        i16x8::from(count).to_array()
    }
}

#[cfg(all(target_feature = "avx2", target_feature = "bmi2"))]
impl BitField {
    pub fn simulate(&mut self) -> RensaResult {
        let mut tracker = RensaNonTracker::new();
        self.simulate_with_tracker(&mut tracker)
    }

    pub fn simulate_fast(&mut self) -> usize {
        let mut tracker = RensaNonTracker::new();
        self.simulate_fast_with_tracker(&mut tracker)
    }

    pub fn simulate_with_tracker<T: RensaTracker>(&mut self, tracker: &mut T) -> RensaResult {
        let escaped = self.escape_invisible();

        let mut score = 0;
        let mut frames = 0;
        let mut quick = false;
        let mut current_chain = 1;

        loop {
            let mut erased = unsafe { FieldBit::uninitialized() };
            let nth_chain_score = self.vanish(current_chain, &mut erased, tracker);
            if nth_chain_score == 0 {
                break;
            }

            current_chain += 1;
            score += nth_chain_score;
            frames += frame::FRAMES_VANISH_ANIMATION;

            let max_drops = unsafe { self.drop_after_vanish(erased, tracker) };
            if max_drops > 0 {
                frames += frame::FRAMES_TO_DROP_FAST[max_drops] + frame::FRAMES_GROUNDING;
            } else {
                quick = true;
            }
        }

        self.recover_invisible(&escaped);
        RensaResult::new(current_chain - 1, score, frames, quick)
    }

    pub fn simulate_fast_with_tracker<T: RensaTracker>(&mut self, tracker: &mut T) -> usize {
        let escaped = self.escape_invisible();
        let mut current_chain = 1;

        let mut erased = unsafe { FieldBit::uninitialized() };
        while self.vanish_fast(current_chain, &mut erased, tracker) {
            current_chain += 1;
            unsafe { self.drop_after_vanish_fast(erased, tracker) };
        }

        self.recover_invisible(&escaped);
        current_chain - 1
    }

    pub fn vanish_fast<T: RensaTracker>(
        &self,
        current_chain: usize,
        erased: &mut FieldBit,
        tracker: &mut T,
    ) -> bool {
        let mut erased256 = unsafe { FieldBit256::empty() };
        let mut did_erase = false;

        // RED (100) & BLUE (101)
        {
            let t = unsafe { self.m[1].andnot(self.m[2]).masked_field_12() };
            let mask = unsafe { FieldBit256::from_low_high(self.m[0].andnot(t), self.m[0] & t) };

            let mut vanishing = unsafe { FieldBit256::uninitialized() };
            if unsafe { mask.find_vanishing_bits(&mut vanishing) } {
                erased256.set_all(vanishing);
                did_erase = true;
            }
        }

        // YELLOW (110) & GREEN (111)
        {
            let t = unsafe { (self.m[1] & self.m[2]).masked_field_12() };
            let mask = unsafe { FieldBit256::from_low_high(self.m[0].andnot(t), self.m[0] & t) };

            let mut vanishing = unsafe { FieldBit256::uninitialized() };
            if unsafe { mask.find_vanishing_bits(&mut vanishing) } {
                erased256.set_all(vanishing);
                did_erase = true;
            }
        }

        if !did_erase {
            *erased = unsafe { FieldBit::empty() };
            return false;
        }

        *erased = unsafe { erased256.low() | erased256.high() };

        unsafe {
            let ojama_erased = erased
                .expand1(self.bits(PuyoColor::OJAMA))
                .masked_field_12();
            erased.set_all(ojama_erased);

            tracker.track_vanish(current_chain, erased, &ojama_erased);
        }

        true
    }

    pub fn vanish<T: RensaTracker>(
        &self,
        current_chain: usize,
        erased: &mut FieldBit,
        tracker: &mut T,
    ) -> usize {
        let mut erased256 = unsafe { FieldBit256::empty() };

        let mut num_erased_puyos = 0;
        let mut num_colors = 0;
        let mut long_bonus_coef = 0;
        let mut did_erase = false;

        for i in 0..2 {
            let t = unsafe {
                (if i == 0 {
                    self.m[1].andnot(self.m[2])
                } else {
                    self.m[1] & self.m[2]
                })
                .masked_field_12()
            };

            let high_mask = self.m[0] & t;
            let low_mask = unsafe { self.m[0].andnot(t) };

            let mask = unsafe { FieldBit256::from_low_high(low_mask, high_mask) };
            let mut vanishing = unsafe { FieldBit256::uninitialized() };
            if !unsafe { mask.find_vanishing_bits(&mut vanishing) } {
                continue;
            }
            erased256.set_all(vanishing);
            did_erase = true;

            let (low_count, high_count) = vanishing.popcount_low_high();

            if high_count > 0 {
                num_colors += 1;
                num_erased_puyos += high_count;
                if high_count <= 7 {
                    long_bonus_coef += score::long_bonus(high_count);
                } else {
                    let high = unsafe { vanishing.high() };
                    // slowpath
                    unsafe {
                        high.iterate_bit_with_masking(|x: FieldBit| -> FieldBit {
                            let expanded = x.expand(&high_mask);
                            long_bonus_coef += score::long_bonus(expanded.popcount());
                            expanded
                        });
                    }
                }
            }

            if low_count > 0 {
                num_colors += 1;
                num_erased_puyos += low_count;
                if low_count <= 7 {
                    long_bonus_coef += score::long_bonus(low_count);
                } else {
                    let low = unsafe { vanishing.low() };
                    // slowpath
                    unsafe {
                        low.iterate_bit_with_masking(|x: FieldBit| -> FieldBit {
                            let expanded = x.expand(&low_mask);
                            long_bonus_coef += score::long_bonus(expanded.popcount());
                            expanded
                        });
                    }
                }
            }
        }

        if !did_erase {
            *erased = unsafe { FieldBit::empty() };
            return 0;
        }

        *erased = unsafe { erased256.low() | erased256.high() };

        let color_bonus_coef = score::color_bonus(num_colors);
        let chain_bonus_coef = score::chain_bonus(current_chain);
        let rensa_bonus_coef =
            score::calculate_rensa_bonus_coef(chain_bonus_coef, long_bonus_coef, color_bonus_coef);

        tracker.track_coef(
            current_chain,
            num_erased_puyos,
            long_bonus_coef,
            color_bonus_coef,
        );

        // Removes ojama.
        unsafe {
            let ojama_erased = erased
                .expand1(self.bits(PuyoColor::OJAMA))
                .masked_field_12();
            erased.set_all(ojama_erased);

            tracker.track_vanish(current_chain, erased, &ojama_erased);
        }

        10 * num_erased_puyos * rensa_bonus_coef
    }

    pub unsafe fn drop_after_vanish<T: RensaTracker>(
        &mut self,
        erased: FieldBit,
        tracker: &mut T,
    ) -> usize {
        // Set 1 at non-empty position.
        // Remove 1 bits from the positions where they are erased.
        let nonempty = _mm_andnot_si128(
            erased.as_m128i(),
            (self.m[0] | self.m[1] | self.m[2]).as_m128i(),
        );

        // Find the holes. The number of holes for each column is the number of
        // drops of the column.
        let holes = _mm_and_si128(sseext::mm_porr_epi16(nonempty), erased.as_m128i());
        let num_holes = sseext::mm_popcnt_epi16(holes);
        let max_drops = sseext::mm_hmax_epu16(num_holes);

        self.drop_after_vanish_fast(erased, tracker);

        max_drops as usize
    }

    pub unsafe fn drop_after_vanish_fast<T: RensaTracker>(
        &mut self,
        erased: FieldBit,
        tracker: &mut T,
    ) {
        let ones = sseext::mm_setone_si128();

        let (old_low_bits, old_high_bits) = {
            let t: u64x2 = _mm_xor_si128(erased.as_m128i(), ones).into();
            (t[0], t[1])
        };

        let (new_low_bits, new_high_bits) = {
            let shifted: u64x4 = {
                let shift = _mm256_cvtepu16_epi32(sseext::mm_popcnt_epi16(erased.as_m128i()));
                let half_ones = _mm256_cvtepu16_epi32(ones);
                let shifted = _mm256_srlv_epi32(half_ones, shift);
                _mm256_packus_epi32(shifted, shifted).into()
            };
            (shifted[0], shifted[2])
        };

        let mut d: [u64x2; 3] = [
            self.m[0].as_m128i().into(),
            self.m[1].as_m128i().into(),
            self.m[2].as_m128i().into(),
        ];

        if new_low_bits != 0xFFFFFFFFFFFFFFFF {
            d[0][0] = _pdep_u64(_pext_u64(d[0][0], old_low_bits), new_low_bits);
            d[1][0] = _pdep_u64(_pext_u64(d[1][0], old_low_bits), new_low_bits);
            d[2][0] = _pdep_u64(_pext_u64(d[2][0], old_low_bits), new_low_bits);
            if new_high_bits != 0xFFFFFFFFFFFFFFFF {
                d[0][1] = _pdep_u64(_pext_u64(d[0][1], old_high_bits), new_high_bits);
                d[1][1] = _pdep_u64(_pext_u64(d[1][1], old_high_bits), new_high_bits);
                d[2][1] = _pdep_u64(_pext_u64(d[2][1], old_high_bits), new_high_bits);
            }
        } else {
            d[0][1] = _pdep_u64(_pext_u64(d[0][1], old_high_bits), new_high_bits);
            d[1][1] = _pdep_u64(_pext_u64(d[1][1], old_high_bits), new_high_bits);
            d[2][1] = _pdep_u64(_pext_u64(d[2][1], old_high_bits), new_high_bits);
        }

        self.m[0] = FieldBit::new(d[0].into());
        self.m[1] = FieldBit::new(d[1].into());
        self.m[2] = FieldBit::new(d[2].into());

        tracker.track_drop(old_low_bits, old_high_bits, new_low_bits, new_high_bits);
    }
}

impl FieldIsEmpty for BitField {
    fn is_empty(&self, x: usize, y: usize) -> bool {
        BitField::is_empty(self, x, y)
    }
}

impl std::fmt::Display for BitField {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        // TODO(mayah): More sophisticated way?
        let mut s = String::new();
        for y in 0..16 {
            for x in 0..8 {
                s.push(self.color(x, 15 - y).to_char());
            }
            s.push('\n');
        }

        write!(f, "{}", s)
    }
}

#[cfg(test)]
mod tests {
    use super::BitField;
    use color::{self, Color, PuyoColor};
    use field;
    use field_bit::FieldBit;

    #[test]
    fn test_initial() {
        let bf = BitField::new();
        for x in 0..8 {
            for y in 0..16 {
                if x == 0 || x == 7 || y == 0 || y == 15 {
                    assert_eq!(bf.color(x, y), PuyoColor::WALL);
                } else {
                    assert_eq!(bf.color(x, y), PuyoColor::EMPTY);
                }
            }
        }
    }

    #[test]
    fn test_from_str() {
        let bf = BitField::from_str(concat!(
            "RGBRGB", // 3
            "RGBRGB", // 2
            "RGBRGB"  // 1
        ));

        assert_eq!(bf.color(1, 1), PuyoColor::RED);
        assert_eq!(bf.color(2, 1), PuyoColor::GREEN);
        assert_eq!(bf.color(3, 1), PuyoColor::BLUE);
        assert_eq!(bf.color(1, 3), PuyoColor::RED);
        assert_eq!(bf.color(2, 3), PuyoColor::GREEN);
        assert_eq!(bf.color(3, 3), PuyoColor::BLUE);
    }

    #[test]
    fn test_set_color() {
        let colors = [
            PuyoColor::EMPTY,
            PuyoColor::OJAMA,
            PuyoColor::WALL,
            PuyoColor::IRON,
            PuyoColor::RED,
            PuyoColor::BLUE,
            PuyoColor::YELLOW,
            PuyoColor::GREEN,
        ];
        let mut bf = BitField::new();

        for c in colors.iter() {
            bf.set_color(1, 1, *c);
            assert_eq!(*c, bf.color(1, 1));
        }
    }

    #[test]
    fn test_is_empty() {
        let bf = BitField::from_str(concat!(
            "RRR..." // 1
        ));

        assert!(!bf.is_empty(1, 1));
        assert!(!bf.is_empty(2, 1));
        assert!(!bf.is_empty(3, 1));
        assert!(bf.is_empty(4, 1));
        assert!(bf.is_empty(5, 1));
        assert!(bf.is_empty(6, 1));
    }

    #[test]
    fn test_is_all_cleared() {
        let mut bf = BitField::new();
        assert!(bf.is_all_cleared());

        bf.set_color(3, 1, PuyoColor::RED);
        assert!(!bf.is_all_cleared());

        bf.set_color(3, 1, PuyoColor::EMPTY);
        bf.set_color(1, 14, PuyoColor::RED);
        assert!(bf.is_all_cleared());
    }

    #[test]
    fn test_each_cell() {
        let bf = BitField::from_str(concat!(
            "&&&&&&", // 6
            "OOOOOO", // 5
            "YYYYYY", // 4
            "BBBBBB", // 3
            "GGGGGG", // 2
            "RRRRRR"  // 1
        ));

        for x in 0..field::MAP_WIDTH {
            for y in 0..field::MAP_HEIGHT {
                for c in color::PuyoColor::all_colors() {
                    assert_eq!(unsafe { bf.bits(*c).get(x, y) }, *c == bf.color(x, y));
                    assert_eq!(bf.is_color(x, y, *c), bf.is_color(x, y, *c));
                }

                assert_eq!(bf.is_normal_color(x, y), bf.is_normal_color(x, y));
            }
        }
    }

    #[test]
    fn test_normal_color_bits() {
        let bf = BitField::from_str("RGO&BY");
        let fb = FieldBit::from_str("11..11");
        assert_eq!(bf.normal_color_bits(), fb);
    }

    #[test]
    fn test_count_connected() {
        let bf = BitField::from_str(concat!(
            "RRRRRR", // 3
            "BYBRRY", // 2
            "RRRBBB"  // 1
        ));

        assert_eq!(bf.count_connected(1, 1), 3);
        assert_eq!(bf.count_connected(4, 1), 3);
        assert_eq!(bf.count_connected(1, 2), 1);
        assert_eq!(bf.count_connected(3, 2), 1);
        assert_eq!(bf.count_connected(6, 2), 1);
        assert_eq!(bf.count_connected(4, 2), 8);

        assert_eq!(bf.count_connected_max4(1, 1), 3);
        assert_eq!(bf.count_connected_max4(4, 1), 3);
        assert_eq!(bf.count_connected_max4(1, 2), 1);
        assert_eq!(bf.count_connected_max4(3, 2), 1);
        assert_eq!(bf.count_connected_max4(6, 2), 1);
        assert!(bf.count_connected_max4(4, 2) >= 4);

        assert_eq!(bf.count_connected_max4_with_color(1, 1, bf.color(1, 1)), 3);
        assert_eq!(bf.count_connected_max4_with_color(4, 1, bf.color(4, 1)), 3);
        assert_eq!(bf.count_connected_max4_with_color(1, 2, bf.color(1, 2)), 1);
        assert_eq!(bf.count_connected_max4_with_color(3, 2, bf.color(3, 2)), 1);
        assert_eq!(bf.count_connected_max4_with_color(6, 2, bf.color(6, 2)), 1);
        assert!(bf.count_connected_max4_with_color(4, 2, bf.color(4, 2)) >= 4);
    }

    #[test]
    fn test_count_connected_puyos_edge_case() {
        let bf = BitField::from_str(concat!(
            ".....R", // 13
            "OOOOOR", // 12
            "OOOOOO", // 11
            "OOOOOO", // 10
            "OOOOOO", // 9
            "OOOOOO", // 8
            "OOOOOO", // 7
            "OOOOOO", // 6
            "OOOOOO", // 5
            "OOOOOO", // 4
            "OOOOOO", // 3
            "OOOOOO", // 2
            "OOOOOO"  // 1
        ));

        assert_eq!(bf.count_connected(6, 12), 1);
        assert_eq!(bf.count_connected_max4(6, 12), 1);
        assert_eq!(
            bf.count_connected_max4_with_color(6, 12, bf.color(6, 12)),
            1
        );

        assert_eq!(bf.count_connected(6, 13), 0);
        assert_eq!(bf.count_connected_max4(6, 13), 0);
        assert_eq!(
            bf.count_connected_max4_with_color(6, 13, bf.color(6, 13)),
            0
        );
    }

    #[test]
    fn test_is_connected() {
        let bf = BitField::from_str(concat!(
            "B.B..Y", // 2
            "RRRBBB", // 1
        ));

        assert!(bf.is_connected(1, 1));
        assert!(bf.is_connected(2, 1));
        assert!(bf.is_connected(3, 1));
        assert!(bf.is_connected(4, 1));
        assert!(bf.is_connected(5, 1));
        assert!(bf.is_connected(6, 1));
        assert!(!bf.is_connected(1, 2));
        assert!(!bf.is_connected(3, 2));
        assert!(!bf.is_connected(6, 2));
    }

    #[test]
    fn test_is_connected_edge_case() {
        let bf = BitField::from_str(concat!(
            ".....R", // 13
            "OOOOOR", // 12
            "OOOOOO", // 11
            "OOOOOO", // 10
            "OOOOOO", // 9
            "OOOOOO", // 8
            "OOOOOO", // 7
            "OOOOOO", // 6
            "OOOOOO", // 5
            "OOOOOO", // 4
            "OOOOOO", // 3
            "OOOOOO", // 2
            "OOOOOO"  // 1
        ));

        assert!(!bf.is_connected(6, 12));
    }

    #[test]
    fn test_calculate_height() {
        let bf = BitField::from_str(concat!(
            ".....O", // 14
            "....OO", // 13
            "...OOO", // 12
            "..OOOO", // 11
            ".OOOOO", // 10
            ".OOOOO", // 9
            ".OOOOO", // 8
            ".OOOOO", // 7
            ".OOOOO", // 6
            ".OOOOO", // 5
            ".OOOOO", // 4
            ".OOOOO", // 3
            ".OOOOO", // 2
            ".OOOOO"  // 1
        ));

        let height = bf.calculate_height();
        assert_eq!(height[1], 0);
        assert_eq!(height[2], 10);
        assert_eq!(height[3], 11);
        assert_eq!(height[4], 12);
        assert_eq!(height[5], 13);
        assert_eq!(height[6], 13); // not 14 but 13
    }
}

#[cfg(all(test, target_feature = "avx2", target_feature = "bmi2"))]
mod tests_simulation {
    use super::BitField;
    use field_bit::FieldBit;
    use frame;
    use rensa_tracker::RensaNonTracker;

    struct SimulationTestcase {
        field: BitField,
        chain: usize,
        score: usize,
        frame: usize,
        quick: bool,
    }

    #[test]
    fn test_simulate() {
        let simulation_testcases = &[
            SimulationTestcase {
                field: BitField::from_str(concat!(
                    ".BBBB." // 1
                )),
                chain: 1,
                score: 40,
                frame: frame::FRAMES_VANISH_ANIMATION,
                quick: true,
            },
            SimulationTestcase {
                field: BitField::from_str(concat!(
                    ".RBRB.", // 4
                    "RBRBR.", // 3
                    "RBRBR.", // 2
                    "RBRBRR"  // 1
                )),
                chain: 5,
                score: 40 + 40 * 8 + 40 * 16 + 40 * 32 + 40 * 64,
                frame: frame::FRAMES_VANISH_ANIMATION * 5
                    + frame::FRAMES_TO_DROP_FAST[3] * 4
                    + frame::FRAMES_GROUNDING * 4,
                quick: true,
            },
            SimulationTestcase {
                field: BitField::from_str(concat!(
                    ".YGGY.", // 4
                    "BBBBBB", // 3
                    "GYBBYG", // 2
                    "BBBBBB"  // 1
                )),
                chain: 1,
                score: 140 * 10,
                frame: frame::FRAMES_VANISH_ANIMATION
                    + frame::FRAMES_TO_DROP_FAST[3]
                    + frame::FRAMES_GROUNDING,
                quick: false,
            },
        ];

        for testcase in simulation_testcases {
            let mut bf = testcase.field.clone();
            let chain = bf.simulate_fast();
            assert_eq!(testcase.chain, chain)
        }

        for testcase in simulation_testcases {
            let mut bf = testcase.field.clone();
            let rensa_result = bf.simulate();
            assert_eq!(testcase.chain, rensa_result.chain);
            assert_eq!(testcase.score, rensa_result.score);
            assert_eq!(testcase.frame, rensa_result.frame);
            assert_eq!(testcase.quick, rensa_result.quick);
        }
    }

    #[test]
    fn test_vanish_1() {
        let bf = BitField::from_str(concat!(
            "..YY..", // 3
            "GGGGYY", // 2
            "RRRROY"  // 1
        ));

        let expected = FieldBit::from_str(concat!(
            "1111..", // 2
            "11111."  // 1
        ));

        let mut vanishing = unsafe { FieldBit::uninitialized() };
        let mut tracker = RensaNonTracker::new();
        assert!(bf.vanish_fast(1, &mut vanishing, &mut tracker));
        assert_eq!(expected, vanishing);

        assert_eq!(bf.vanish(1, &mut vanishing, &mut tracker), 80 * 3);
        assert_eq!(expected, vanishing);
    }

    #[test]
    fn test_vanish_2() {
        let bf = BitField::from_str(concat!(
            "OOOOOO", // 3
            "OOGGOO", // 2
            "OOGGOO"  // 1
        ));

        let expected = FieldBit::from_str(concat!(
            "..11..", // 3
            ".1111.", // 2
            ".1111."  // 1
        ));

        let mut vanishing = unsafe { FieldBit::uninitialized() };
        let mut tracker = RensaNonTracker::new();
        assert!(bf.vanish_fast(1, &mut vanishing, &mut tracker));
        assert_eq!(expected, vanishing);

        assert_eq!(bf.vanish(1, &mut vanishing, &mut tracker), 40);
        assert_eq!(expected, vanishing);
    }

    #[test]
    fn test_vanish_3() {
        let bf = BitField::from_str(concat!(
            "....RR", // 13
            "OO.ORR", // 12
            "OOOOOO", // 11
            "OOOOOO", // 10
            "OOOOOO", // 9
            "OOOOOO", // 8
            "OOOOOO", // 7
            "OOOOOO", // 6
            "OOOOOO", // 5
            "OOOOOO", // 4
            "OOOOOO", // 3
            "OOOOOO", // 2
            "OOOOOO"  // 1
        ));

        let mut vanishing = unsafe { FieldBit::uninitialized() };
        let mut tracker = RensaNonTracker::new();
        assert!(!bf.vanish_fast(1, &mut vanishing, &mut tracker));
        assert_eq!(bf.vanish(1, &mut vanishing, &mut tracker), 0);
    }

    #[test]
    fn test_drop_after_vanish_fast() {
        let mut bf = BitField::from_str(concat!(
            "..BB..", // 2
            "RRRR.."  // 1
        ));
        let erased = FieldBit::from_str(concat!(
            "1111.." // 1
         ));

        let mut tracker = RensaNonTracker::new();

        let invisible = bf.escape_invisible();
        unsafe { bf.drop_after_vanish_fast(erased, &mut tracker) };
        bf.recover_invisible(&invisible);

        let expected = BitField::from_str(concat!(
            "..BB.." // 1
        ));

        assert_eq!(expected, bf);
    }
}
