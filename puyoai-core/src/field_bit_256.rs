use field_bit::FieldBit;
use std;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

#[derive(Clone, Copy, Debug)]
pub struct FieldBit256 {
    m: __m256i,
}

impl FieldBit256 {
    pub fn new(m: __m256i) -> FieldBit256 {
        FieldBit256 { m: m }
    }

    pub unsafe fn uninitialized() -> FieldBit256 {
        std::mem::uninitialized::<FieldBit256>()
    }

    pub unsafe fn empty() -> FieldBit256 {
        FieldBit256 {
            m: _mm256_setzero_si256(),
        }
    }

    pub unsafe fn from_low_high(low: FieldBit, high: FieldBit) -> FieldBit256 {
        let m = _mm256_inserti128_si256(_mm256_castsi128_si256(low.as_m128i()), high.as_m128i(), 1);
        FieldBit256 { m: m }
    }

    #[allow(dead_code)]
    pub fn get_low(&self, x: usize, y: usize) -> bool {
        unsafe { self.low().get(x, y) }
    }

    #[allow(dead_code)]
    pub fn get_high(&self, x: usize, y: usize) -> bool {
        unsafe { self.high().get(x, y) }
    }

    pub unsafe fn low(&self) -> FieldBit {
        FieldBit::new(_mm256_castsi256_si128(self.m))
    }

    pub unsafe fn high(&self) -> FieldBit {
        FieldBit::new(_mm256_extracti128_si256(self.m, 1))
    }

    #[allow(dead_code)]
    pub fn set_low(&mut self, x: usize, y: usize) {
        self.m = unsafe { _mm256_or_si256(self.m, FieldBit256::onebit_low(x, y)) }
    }

    #[allow(dead_code)]
    pub fn set_high(&mut self, x: usize, y: usize) {
        self.m = unsafe { _mm256_or_si256(self.m, FieldBit256::onebit_high(x, y)) }
    }

    pub fn set_all(&mut self, fb: FieldBit256) {
        self.m = unsafe { _mm256_or_si256(self.m, fb.m) }
    }

    #[allow(dead_code)]
    pub unsafe fn expand(&self, mask: FieldBit256) -> FieldBit256 {
        let mut seed = self.m;

        loop {
            let mut expanded = seed;
            expanded = _mm256_or_si256(_mm256_slli_epi16(seed, 1), expanded);
            expanded = _mm256_or_si256(_mm256_srli_epi16(seed, 1), expanded);
            expanded = _mm256_or_si256(_mm256_slli_si256(seed, 2), expanded);
            expanded = _mm256_or_si256(_mm256_srli_si256(seed, 2), expanded);
            expanded = _mm256_and_si256(mask.m, expanded);

            if _mm256_testc_si256(seed, expanded) != 0 {
                // seed == expanded
                return FieldBit256::new(expanded);
            }
            seed = expanded;
        }
    }

    pub unsafe fn expand1(&self, mask: FieldBit256) -> FieldBit256 {
        let v1 = _mm256_slli_si256(self.m, 2);
        let v2 = _mm256_srli_si256(self.m, 2);
        let v3 = _mm256_slli_epi16(self.m, 1);
        let v4 = _mm256_srli_epi16(self.m, 1);

        FieldBit256::new(_mm256_and_si256(
            _mm256_or_si256(
                _mm256_or_si256(_mm256_or_si256(self.m, v1), _mm256_or_si256(v2, v3)),
                v4,
            ),
            mask.m,
        ))
    }

    pub unsafe fn find_vanishing_bits(&self, vanishing: &mut FieldBit256) -> bool {
        let m = self.m;
        let u = _mm256_and_si256(_mm256_srli_epi16(m, 1), m);
        let d = _mm256_and_si256(_mm256_slli_epi16(m, 1), m);
        let l = _mm256_and_si256(_mm256_slli_si256(m, 2), m);
        let r = _mm256_and_si256(_mm256_srli_si256(m, 2), m);

        let ud_and = _mm256_and_si256(u, d);
        let lr_and = _mm256_and_si256(l, r);
        let ud_or = _mm256_or_si256(u, d);
        let lr_or = _mm256_or_si256(l, r);

        let twos = _mm256_or_si256(
            _mm256_or_si256(lr_and, ud_and),
            _mm256_and_si256(ud_or, lr_or),
        );
        let two_d = _mm256_and_si256(_mm256_slli_epi16(twos, 1), twos);
        let two_l = _mm256_and_si256(_mm256_slli_si256(twos, 2), twos);
        let threes = _mm256_or_si256(
            _mm256_and_si256(ud_and, lr_or),
            _mm256_and_si256(lr_and, ud_or),
        );
        let t = _mm256_or_si256(_mm256_or_si256(two_d, two_l), threes);

        if _mm256_testz_si256(t, t) != 0 {
            *vanishing = FieldBit256::empty();
            return false;
        }

        let two_u = _mm256_and_si256(_mm256_srli_epi16(twos, 1), twos);
        let two_r = _mm256_and_si256(_mm256_srli_si256(twos, 2), twos);
        *vanishing =
            FieldBit256::new(_mm256_or_si256(_mm256_or_si256(t, two_u), two_r)).expand1(*self);
        true
    }

    pub fn popcount_low_high(&self) -> (usize, usize) {
        unsafe { (self.low().popcount(), self.high().popcount()) }
    }

    fn check_in_range(x: usize, y: usize) -> bool {
        x < 8 && y < 16
    }

    unsafe fn onebit_low(x: usize, y: usize) -> __m256i {
        debug_assert!(FieldBit256::check_in_range(x, y));

        let shift = ((x << 4) | y) & 0x3F;
        let zero = _mm256_setzero_si256();
        if x < 4 {
            return _mm256_insert_epi64(zero, 1 << shift, 0);
        } else {
            return _mm256_insert_epi64(zero, 1 << shift, 1);
        }
    }

    unsafe fn onebit_high(x: usize, y: usize) -> __m256i {
        debug_assert!(FieldBit256::check_in_range(x, y));

        let shift = ((x << 4) | y) & 0x3F;
        let zero = _mm256_setzero_si256();
        if x < 4 {
            return _mm256_insert_epi64(zero, 1 << shift, 2);
        } else {
            return _mm256_insert_epi64(zero, 1 << shift, 3);
        }
    }
}

impl std::ops::BitOr for FieldBit256 {
    type Output = FieldBit256;

    fn bitor(self, rhs: FieldBit256) -> FieldBit256 {
        FieldBit256::new(unsafe { _mm256_or_si256(self.m, rhs.m) })
    }
}

impl std::ops::BitAnd for FieldBit256 {
    type Output = FieldBit256;

    fn bitand(self, rhs: FieldBit256) -> FieldBit256 {
        FieldBit256::new(unsafe { _mm256_and_si256(self.m, rhs.m) })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field;
    use field_bit::FieldBit;

    #[test]
    fn test_constructor() {
        let fb256 = unsafe { FieldBit256::empty() };

        for x in 0..8 {
            for y in 0..16 {
                assert!(!fb256.get_low(x, y));
                assert!(!fb256.get_high(x, y));
            }
        }
    }

    #[test]
    fn test_from_low_high() {
        let mut low = unsafe { FieldBit::empty() };
        let mut high = unsafe { FieldBit::empty() };
        unsafe {
            low.set(1, 3);
            low.set(4, 8);
            high.set(2, 4);
            high.set(5, 9);
        }

        let fb256 = unsafe { FieldBit256::from_low_high(low, high) };
        assert!(fb256.get_low(1, 3));
        assert!(fb256.get_low(4, 8));
        assert!(fb256.get_high(2, 4));
        assert!(fb256.get_high(5, 9));

        assert!(!fb256.get_high(1, 3));
        assert!(!fb256.get_high(4, 8));
        assert!(!fb256.get_low(2, 4));
        assert!(!fb256.get_low(5, 9));

        assert_eq!(low, unsafe { fb256.low() });
        assert_eq!(high, unsafe { fb256.high() });
    }

    #[test]
    fn test_expand() {
        let mask_high = FieldBit::from_str(concat!(
            "......", // 5
            "11..11", // 4
            "11..11", // 3
            "......", // 2
            "111111"  // 1
        ));
        let mask_low = FieldBit::from_str(concat!(
            "111111", // 5
            ".....1", // 4
            "111111", // 3
            "1.....", // 2
            "111111"  // 1
        ));

        let expected_high = FieldBit::from_str(concat!(
             "111111" // 1
        ));
        let expected_low = mask_low;

        let mask = unsafe { FieldBit256::from_low_high(mask_low, mask_high) };

        let mut bit = unsafe { FieldBit256::empty() };
        bit.set_high(3, 1);
        bit.set_low(6, 1);

        let expanded = unsafe { bit.expand(mask) };
        assert_eq!(expected_high, unsafe { expanded.high() });
        assert_eq!(expected_low, unsafe { expanded.low() });
    }

    #[test]
    fn test_find_vanishing_bits_1() {
        let fb256 = {
            let f = FieldBit::from_str(concat!(
                ".1....", // 6
                "11..1.", // 5
                ".1.111", // 4
                "1...1.", // 3
                "11.111", // 2
                "1...1."  // 1
            ));
            unsafe { FieldBit256::from_low_high(f, f) }
        };

        let mut vanishing = unsafe { FieldBit256::uninitialized() };
        assert!(unsafe { fb256.find_vanishing_bits(&mut vanishing) });

        for x in 1..field::WIDTH + 1 {
            for y in 1..field::HEIGHT + 1 {
                assert_eq!(
                    vanishing.get_low(x, y),
                    fb256.get_low(x, y),
                    "x={}, y={}",
                    x,
                    y
                );
                assert_eq!(
                    vanishing.get_high(x, y),
                    fb256.get_high(x, y),
                    "x={}, y={}",
                    x,
                    y
                );
            }
        }
    }

    #[test]
    fn test_find_vanishing_bits_2() {
        let fb256 = {
            let f = FieldBit::from_str(concat!(
                ".....1", // 4
                ".111.1", // 3
                ".....1", // 2
                ".1.11."  // 1
            ));
            unsafe { FieldBit256::from_low_high(f, f) }
        };

        let mut vanishing = unsafe { FieldBit256::uninitialized() };
        assert!(!unsafe { fb256.find_vanishing_bits(&mut vanishing) });

        for x in 1..field::WIDTH + 1 {
            for y in 1..field::HEIGHT + 1 {
                assert!(!vanishing.get_low(x, y));
                assert!(!vanishing.get_high(x, y));
            }
        }
    }

    #[test]
    fn test_iterate_bit_with_masking() {
        let mut bf = unsafe { FieldBit::empty() };
        unsafe {
            bf.set(1, 2);
            bf.set(2, 3);
            bf.set(3, 4);
            bf.set(4, 5);
            bf.set(5, 6);
            bf.set(6, 7);
        }

        assert_eq!(6, bf.popcount());

        let mut count = 0;
        let mut iterated = unsafe { FieldBit::empty() };
        unsafe {
            bf.iterate_bit_with_masking(|x: FieldBit| -> FieldBit {
                iterated.set_all(x);
                assert_eq!(1, x.popcount());
                count += 1;

                x
            });
        }

        assert_eq!(6, count);
        assert_eq!(bf, iterated);
    }
}
