use sseext;
use std;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;
use std::simd::*;

#[derive(Clone, Copy, Debug)]
pub struct FieldBit {
    m: __m128i,
}

impl FieldBit {
    pub fn new(m: __m128i) -> FieldBit {
        FieldBit { m: m }
    }

    pub unsafe fn uninitialized() -> FieldBit {
        std::mem::uninitialized::<FieldBit>()
    }

    pub unsafe fn empty() -> FieldBit {
        FieldBit {
            m: _mm_setzero_si128(),
        }
    }

    pub unsafe fn from_values(
        v1: u16,
        v2: u16,
        v3: u16,
        v4: u16,
        v5: u16,
        v6: u16,
        v7: u16,
        v8: u16,
    ) -> FieldBit {
        FieldBit {
            m: _mm_setr_epi16(
                v1 as i16, v2 as i16, v3 as i16, v4 as i16, v5 as i16, v6 as i16, v7 as i16,
                v8 as i16,
            ),
        }
    }

    pub fn from_onebit(x: usize, y: usize) -> FieldBit {
        FieldBit {
            m: unsafe { FieldBit::onebit(x, y) },
        }
    }

    pub fn from_str(s: &str) -> FieldBit {
        let mut f = unsafe { FieldBit::empty() };

        assert!(s.len() % 6 == 0);

        let mut cnt = 0;
        for b in s.bytes().rev() {
            let x = 6 - (cnt % 6);
            let y = (cnt / 6) + 1;
            if b == b'1' {
                unsafe { f.set(x, y) };
            }
            cnt += 1;
        }

        f
    }

    pub fn as_m128i(&self) -> __m128i {
        self.m
    }

    pub unsafe fn get(&self, x: usize, y: usize) -> bool {
        debug_assert!(FieldBit::check_in_range(x, y));
        _mm_testz_si128(FieldBit::onebit(x, y), self.m) == 0
    }

    pub unsafe fn set(&mut self, x: usize, y: usize) {
        debug_assert!(FieldBit::check_in_range(x, y));
        self.m = _mm_or_si128(FieldBit::onebit(x, y), self.m)
    }

    pub unsafe fn set_all(&mut self, fb: FieldBit) {
        self.m = _mm_or_si128(self.m, fb.m)
    }

    pub unsafe fn unset(&mut self, x: usize, y: usize) {
        debug_assert!(FieldBit::check_in_range(x, y));
        self.m = _mm_andnot_si128(FieldBit::onebit(x, y), self.m)
    }

    pub unsafe fn is_empty(&self) -> bool {
        _mm_testz_si128(self.m, self.m) != 0
    }

    pub fn mask(&self, mask: FieldBit) -> FieldBit {
        *self & mask
    }

    pub unsafe fn not_mask(&self, mask: FieldBit) -> FieldBit {
        FieldBit::new(_mm_andnot_si128(mask.m, self.m))
    }

    pub unsafe fn andnot(&self, other: FieldBit) -> FieldBit {
        FieldBit::new(_mm_andnot_si128(self.m, other.m))
    }

    pub unsafe fn masked_field_12(&self) -> FieldBit {
        FieldBit {
            m: _mm_and_si128(
                self.m,
                _mm_setr_epi16(0, 0x1FFE, 0x1FFE, 0x1FFE, 0x1FFE, 0x1FFE, 0x1FFE, 0),
            ),
        }
    }

    pub unsafe fn masked_field_13(&self) -> FieldBit {
        FieldBit {
            m: _mm_and_si128(
                self.m,
                _mm_setr_epi16(0, 0x3FFE, 0x3FFE, 0x3FFE, 0x3FFE, 0x3FFE, 0x3FFE, 0),
            ),
        }
    }

    pub unsafe fn not_masked_field_13(&self) -> FieldBit {
        let r = _mm_xor_si128(
            sseext::mm_setone_si128(),
            _mm_setr_epi16(0, 0x3FFE, 0x3FFE, 0x3FFE, 0x3FFE, 0x3FFE, 0x3FFE, 0),
        );
        FieldBit {
            m: _mm_and_si128(self.m, r),
        }
    }

    /// Returns true if there are 4-connected bits.
    /// Such bits are copied to `vanishing`.
    pub unsafe fn find_vanishing_bits(&self, vanishing: &mut FieldBit) -> bool {
        //  x
        // xox              -- o is 3-connected
        //
        // xoox  ox   x oo
        //      xo  xoo oo  -- o is 2-connected.
        //
        // So, one 3-connected piece or two 2-connected pieces are necessary and sufficient.
        //
        // Also, 1-connected won't be connected to each other in vanishing case.
        // So, after this, expand1() should be enough.

        let u = _mm_and_si128(_mm_srli_epi16(self.m, 1), self.m);
        let d = _mm_and_si128(_mm_slli_epi16(self.m, 1), self.m);
        let l = _mm_and_si128(_mm_slli_si128(self.m, 2), self.m);
        let r = _mm_and_si128(_mm_srli_si128(self.m, 2), self.m);

        let ud_and = _mm_and_si128(u, d);
        let lr_and = _mm_and_si128(l, r);
        let ud_or = _mm_or_si128(u, d);
        let lr_or = _mm_or_si128(l, r);

        let threes = _mm_or_si128(_mm_and_si128(ud_and, lr_or), _mm_and_si128(lr_and, ud_or));
        let twos = _mm_or_si128(_mm_or_si128(ud_and, lr_and), _mm_and_si128(ud_or, lr_or));

        let two_d = _mm_and_si128(_mm_slli_epi16(twos, 1), twos);
        let two_l = _mm_and_si128(_mm_slli_si128(twos, 2), twos);

        let mut t = _mm_or_si128(_mm_or_si128(threes, two_d), two_l);
        if _mm_testz_si128(t, t) != 0 {
            *vanishing = FieldBit::empty();
            return false;
        }

        let two_u = _mm_and_si128(_mm_srli_epi16(twos, 1), twos);
        let two_r = _mm_and_si128(_mm_srli_si128(twos, 2), twos);
        t = _mm_or_si128(_mm_or_si128(t, two_u), two_r);

        *vanishing = FieldBit::new(t).expand1(*self);
        true
    }

    pub unsafe fn has_vanishing_bits(&self) -> bool {
        let u = _mm_and_si128(_mm_srli_epi16(self.m, 1), self.m);
        let d = _mm_and_si128(_mm_slli_epi16(self.m, 1), self.m);
        let l = _mm_and_si128(_mm_slli_si128(self.m, 2), self.m);
        let r = _mm_and_si128(_mm_srli_si128(self.m, 2), self.m);

        let ud_and = _mm_and_si128(u, d);
        let lr_and = _mm_and_si128(l, r);
        let ud_or = _mm_or_si128(u, d);
        let lr_or = _mm_or_si128(l, r);

        let threes = _mm_or_si128(_mm_and_si128(ud_and, lr_or), _mm_and_si128(lr_and, ud_or));
        let twos = _mm_or_si128(_mm_or_si128(ud_and, lr_and), _mm_and_si128(ud_or, lr_or));

        let two_d = _mm_and_si128(_mm_slli_epi16(twos, 1), twos);
        let two_l = _mm_and_si128(_mm_slli_si128(twos, 2), twos);

        let vanishing = _mm_or_si128(_mm_or_si128(threes, two_d), two_l);
        _mm_testz_si128(vanishing, vanishing) == 0
    }

    pub fn popcount(&self) -> usize {
        let (low, high) = {
            let x: u64x2 = self.m.into();
            (x[0], x[1])
        };
        (low.count_ones() + high.count_ones()) as usize
    }

    pub unsafe fn expand(&self, mask: &FieldBit) -> FieldBit {
        let mut seed = self.m;
        loop {
            let mut expanded = seed;
            expanded = _mm_or_si128(_mm_slli_epi16(seed, 1), expanded);
            expanded = _mm_or_si128(_mm_srli_epi16(seed, 1), expanded);
            expanded = _mm_or_si128(_mm_slli_si128(seed, 2), expanded);
            expanded = _mm_or_si128(_mm_srli_si128(seed, 2), expanded);
            expanded = _mm_and_si128(mask.m, expanded);

            if _mm_testc_si128(seed, expanded) != 0 {
                // seed == expanded
                return FieldBit::new(expanded);
            }
            seed = expanded;
        }
    }

    pub unsafe fn expand1(&self, mask: FieldBit) -> FieldBit {
        let seed = self.m;
        let v1 = _mm_slli_epi16(seed, 1);
        let v2 = _mm_srli_epi16(seed, 1);
        let v3 = _mm_slli_si128(seed, 2);
        let v4 = _mm_srli_si128(seed, 2);

        let m = _mm_and_si128(
            _mm_or_si128(
                _mm_or_si128(_mm_or_si128(seed, v1), _mm_or_si128(v2, v3)),
                v4,
            ),
            mask.m,
        );
        FieldBit { m: m }
    }

    /// Returns bits where edge is expanded.
    /// This might contain the original bits, so you'd like to take mask.
    ///
    /// ```text
    /// ......      ..xx..    ..xx..
    /// ..xx..  --> .x..x. or .xxxx.
    /// ......      ..xx..    ..xx..
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use puyoai_core::field_bit::FieldBit;
    /// let fb = FieldBit::from_str(concat!(
    ///     "......",
    ///     "..11..",
    ///     "......"));
    /// let expected = FieldBit::from_str(concat!(
    ///     "..11..",
    ///     ".1111.",
    ///     "..11.."));
    /// assert_eq!(expected, unsafe { fb.expand_edge() } | fb);
    /// ```
    pub unsafe fn expand_edge(&self) -> FieldBit {
        let seed = self.m;
        let m1 = _mm_slli_epi16(seed, 1);
        let m2 = _mm_srli_epi16(seed, 1);
        let m3 = _mm_slli_si128(seed, 2);
        let m4 = _mm_srli_si128(seed, 2);

        return FieldBit::new(_mm_or_si128(_mm_or_si128(m1, m2), _mm_or_si128(m3, m4)));
    }

    pub unsafe fn iterate_bit_with_masking<F: FnMut(FieldBit) -> FieldBit>(&self, mut callback: F) {
        let zero = _mm_setzero_si128();
        let down_ones = _mm_cvtsi64_si128(-1 as i64);
        let up_ones = _mm_slli_si128(down_ones, 8);

        let mut current = self.m;

        // upper is zero?
        while _mm_testz_si128(up_ones, current) == 0 {
            // y = x & (-x)
            let y = _mm_and_si128(current, _mm_sub_epi64(zero, current));
            let z = _mm_and_si128(up_ones, y);
            let mask = callback(FieldBit::new(z));
            current = _mm_andnot_si128(mask.as_m128i(), current);
        }

        while _mm_testz_si128(down_ones, current) == 0 {
            // y = x & (-x)
            let y = _mm_and_si128(current, _mm_sub_epi64(zero, current));
            let z = _mm_and_si128(down_ones, y);
            let mask = callback(FieldBit::new(z));
            current = _mm_andnot_si128(mask.as_m128i(), current);
        }
    }

    pub fn iterate_bit_position<F>(&self, mut callback: F)
    where
        F: FnMut(usize, usize),
    {
        let (mut low, mut high) = {
            let x: u64x2 = self.m.into();
            (x[0], x[1])
        };

        while low != 0 {
            let bit = low.trailing_zeros();
            let x = bit >> 4;
            let y = bit & 0xF;
            callback(x as usize, y as usize);
            low = low & (low - 1);
        }

        while high != 0 {
            let bit = high.trailing_zeros();
            let x = 4 + (bit >> 4);
            let y = bit & 0xF;
            callback(x as usize, y as usize);
            high = high & (high - 1);
        }
    }

    fn check_in_range(x: usize, y: usize) -> bool {
        x < 8 && y < 16
    }

    unsafe fn onebit(x: usize, y: usize) -> __m128i {
        debug_assert!(FieldBit::check_in_range(x, y));

        let shift = ((x << 4) | y) & 0x3F;
        let hi: i64 = (x as i64) >> 2;
        let lo: i64 = hi ^ 1;

        _mm_set_epi64x(hi << shift, lo << shift)
    }
}

impl std::ops::BitOr for FieldBit {
    type Output = FieldBit;

    fn bitor(self, rhs: FieldBit) -> FieldBit {
        FieldBit::new(unsafe { _mm_or_si128(self.m, rhs.m) })
    }
}

impl std::ops::BitAnd for FieldBit {
    type Output = FieldBit;

    fn bitand(self, rhs: FieldBit) -> FieldBit {
        FieldBit::new(unsafe { _mm_and_si128(self.m, rhs.m) })
    }
}

impl std::cmp::PartialEq<FieldBit> for FieldBit {
    fn eq(&self, other: &FieldBit) -> bool {
        let x = unsafe { _mm_xor_si128(self.m, other.m) };
        unsafe { _mm_testz_si128(x, x) == 1 }
    }
}

impl std::fmt::Display for FieldBit {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let x: u16x8 = self.m.into();
        write!(
            f,
            "({}, {}, {}, {}, {}, {}, {}, {})",
            x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]
        )
    }
}

#[cfg(test)]
mod tests {
    use field;
    use field_bit::FieldBit;

    #[test]
    fn test_empty() {
        let fb = unsafe { FieldBit::empty() };
        for x in 0..8 {
            for y in 0..16 {
                assert_eq!(unsafe { fb.get(x, y) }, false);
            }
        }
    }

    #[test]
    fn test_from_value() {
        let fb = unsafe {
            FieldBit::from_values(
                1 << 0,
                1 << 1,
                1 << 2,
                1 << 3,
                1 << 4,
                1 << 5,
                1 << 6,
                1 << 7,
            )
        };
        for x in 0..8 {
            for y in 0..16 {
                assert_eq!(
                    unsafe { fb.get(x, y) },
                    x == y,
                    "failed at x={}, y={}, fb.get(x, y)={}",
                    x,
                    y,
                    unsafe { fb.get(x, y) }
                );
            }
        }
    }

    #[test]
    fn test_from_str() {
        let fb = FieldBit::from_str(concat!(
            "111...", // 3
            "......", // 2
            "111..."  // 1
        ));

        for x in 0..8 {
            for y in 0..16 {
                let b = (y == 1 || y == 3) && (1 <= x && x <= 3);
                assert_eq!(unsafe { fb.get(x, y) }, b, "x={}, y={}", x, y);
            }
        }
    }

    #[test]
    fn test_set_get() {
        for x in 0..8 {
            for y in 0..16 {
                unsafe {
                    let mut fb = FieldBit::empty();
                    assert!(!fb.get(x, y));
                    fb.set(x, y);
                    assert!(fb.get(x, y));
                    fb.unset(x, y);
                    assert!(!fb.get(x, y));
                }
            }
        }
    }

    #[test]
    fn test_masked_field() {
        let fb = unsafe {
            FieldBit::from_values(
                0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF,
            )
        };
        let fb12 = unsafe { fb.masked_field_12() };
        let fb13 = unsafe { fb.masked_field_13() };

        for x in 0..field::MAP_WIDTH {
            for y in 0..field::MAP_HEIGHT {
                assert!(unsafe { fb.get(x, y) }, "x={}, y={}", x, y);
                assert_eq!(
                    unsafe { fb12.get(x, y) },
                    1 <= x && x <= 6 && 1 <= y && y <= 12,
                    "x={}, y={}",
                    x,
                    y
                );
                assert_eq!(
                    unsafe { fb13.get(x, y) },
                    1 <= x && x <= 6 && 1 <= y && y <= 13,
                    "x={}, y={}",
                    x,
                    y
                );
            }
        }
    }

    #[test]
    fn test_popcount() {
        let fb = unsafe { FieldBit::from_values(1, 2, 3, 4, 5, 6, 7, 8) };
        assert_eq!(fb.popcount(), 1 + 1 + 2 + 1 + 2 + 2 + 3 + 1)
    }

    #[test]
    fn test_expand() {
        let mask = FieldBit::from_str(concat!(
            ".1....", // 4
            "1.11..", // 3
            "1.1...", // 2
            "1.1...", // 1
        ));

        let expected = FieldBit::from_str(concat!(
            "..11..", // 3
            "..1...", // 2
            "..1..."  // 1
        ));

        let actual = unsafe { FieldBit::from_onebit(3, 1).expand(&mask) };
        for x in 0..8 {
            for y in 0..16 {
                assert_eq!(
                    unsafe { actual.get(x, y) },
                    unsafe { expected.get(x, y) },
                    "x={}, y={}",
                    x,
                    y
                );
            }
        }
    }

    #[test]
    fn test_expand1() {
        let mask = FieldBit::from_str(concat!(
            "111111", // 3
            "111111", // 2
            "111111"  // 1
        ));

        let seed = FieldBit::from_str(concat!(
            "......", // 3
            "1...1.", // 2
            "......"  // 1
        ));

        let expected = FieldBit::from_str(concat!(
            "1...1.", // 3
            "11.111", // 2
            "1...1."  // 1
        ));

        let actual = unsafe { seed.expand1(mask) };
        for x in 0..8 {
            for y in 0..16 {
                assert_eq!(
                    unsafe { actual.get(x, y) },
                    unsafe { expected.get(x, y) },
                    "x={}, y={}",
                    x,
                    y
                );
            }
        }
    }

    #[test]
    fn test_is_empty() {
        let fb1 = unsafe { FieldBit::empty() };
        assert!(unsafe { fb1.is_empty() });

        let fb2 = FieldBit::from_onebit(1, 3);
        assert!(!unsafe { fb2.is_empty() });
    }

    #[test]
    fn test_set_all() {
        let mut fb = unsafe { FieldBit::empty() };
        let fb1 = FieldBit::from_onebit(1, 3);
        let fb2 = FieldBit::from_onebit(2, 4);
        unsafe { fb.set_all(fb1) };
        unsafe { fb.set_all(fb2) };

        assert!(unsafe { fb.get(1, 3) });
        assert!(unsafe { fb.get(2, 4) });
        assert!(!unsafe { fb.get(1, 4) });
        assert!(!unsafe { fb.get(2, 3) });
    }

    #[test]
    fn test_find_vanishing_bits_1() {
        let f = FieldBit::from_str(concat!(
            ".1....", // 6
            "11..1.", // 5
            ".1.111", // 4
            "1...1.", // 3
            "11.111", // 2
            "1...1."  // 1
        ));

        let mut vanishing = unsafe { FieldBit::uninitialized() };
        assert!(unsafe { f.has_vanishing_bits() });
        assert!(unsafe { f.find_vanishing_bits(&mut vanishing) });

        for x in 1..field::WIDTH + 1 {
            for y in 1..field::HEIGHT + 1 {
                assert_eq!(
                    unsafe { vanishing.get(x, y) },
                    unsafe { f.get(x, y) },
                    "x={}, y={}",
                    x,
                    y
                );
            }
        }
    }

    #[test]
    fn test_find_vanishing_bits_2() {
        let f = FieldBit::from_str(concat!(
            ".....1", // 4
            ".111.1", // 3
            ".....1", // 2
            ".1.11."  // 1
        ));

        let mut vanishing = unsafe { FieldBit::uninitialized() };
        assert!(!unsafe { f.has_vanishing_bits() });
        assert!(!unsafe { f.find_vanishing_bits(&mut vanishing) });

        for x in 1..field::WIDTH + 1 {
            for y in 1..field::HEIGHT + 1 {
                assert!(!unsafe { vanishing.get(x, y) });
            }
        }
    }

    #[test]
    fn test_eq() {
        let fb1 = FieldBit::from_str(concat!(
            "1....1", // 3
            "1....1", // 2
            "111111"  // 1
        ));
        let fb2 = FieldBit::from_str(concat!(
            "111111", // 3
            "1....1", // 2
            "1....1"  // 1
        ));

        assert!(fb1 == fb1);
        assert!(fb2 == fb2);
        assert!(fb1 != fb2);
    }

    #[test]
    fn test_bit() {
        let fb1 = FieldBit::from_str(concat!(
            "1....1", // 3
            "1....1", // 2
            "111111"  // 1
        ));
        let fb2 = FieldBit::from_str(concat!(
            "111111", // 3
            "1....1", // 2
            "1....1"  // 1
        ));

        let expected_and = FieldBit::from_str(concat!(
            "1....1", // 3
            "1....1", // 2
            "1....1"  // 1
        ));
        let expected_or = FieldBit::from_str(concat!(
            "111111", // 3
            "1....1", // 2
            "111111"  // 1
        ));

        assert_eq!(expected_and, fb1 & fb2);
        assert_eq!(expected_or, fb1 | fb2);
    }

    #[test]
    fn test_iterate_bit_position() {
        let bf = FieldBit::from_str(concat!(
            "...1..", // 6
            ".1....", // 5
            "......", // 4
            "..1...", // 3
            "...1..", // 2
            "1.....", // 1
        ));

        let mut s = Vec::new();
        bf.iterate_bit_position(|x, y| {
            s.push((x, y));
        });
        s.sort();

        assert_eq!(&[(1, 1), (2, 5), (3, 3), (4, 2), (4, 6)], s.as_slice());
    }
}
