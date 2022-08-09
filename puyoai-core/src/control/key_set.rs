use control::Key;

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct KeySet {
    keys: usize, // bit flags
}

impl KeySet {
    pub fn new() -> KeySet {
        KeySet { keys: 0 }
    }

    pub fn from_key(k: Key) -> KeySet {
        let mut ks = KeySet::new();
        ks.set_key(k);
        ks
    }

    pub fn from_keys(keys: &[Key]) -> KeySet {
        let mut ks = KeySet::new();
        for k in keys {
            ks.set_key(*k);
        }
        ks
    }

    pub fn set_key(&mut self, k: Key) {
        self.keys = self.keys | (1 << (k as usize))
    }

    pub fn has_key(&self, k: Key) -> bool {
        (self.keys & (1 << (k as usize))) != 0
    }

    pub fn has_turn_key(&self) -> bool {
        self.has_key(Key::RightTurn) || self.has_key(Key::LeftTurn)
    }

    pub fn has_arrow_key(&self) -> bool {
        self.has_key(Key::Right)
            || self.has_key(Key::Left)
            || self.has_key(Key::Up)
            || self.has_key(Key::Down)
    }

    pub fn to_string(&self) -> String {
        let mut s: String = "".to_string();
        if self.has_key(Key::Up) {
            s += "^";
        }
        if self.has_key(Key::Right) {
            s += ">";
        }
        if self.has_key(Key::Down) {
            s += "v";
        }
        if self.has_key(Key::Left) {
            s += "<";
        }
        if self.has_key(Key::RightTurn) {
            s += "A";
        }
        if self.has_key(Key::LeftTurn) {
            s += "B";
        }
        if self.has_key(Key::Start) {
            s += "S";
        }
        s
    }
}

pub fn parse_keysetseq(s: &str) -> Result<Vec<KeySet>, String> {
    let mut keysetseq = Vec::new();
    for x in s.split(',') {
        let mut ks = KeySet::new();
        for c in x.chars() {
            ks.set_key(Key::parse_char(c)?)
        }
        keysetseq.push(ks);
    }
    Ok(keysetseq)
}

pub fn keysetseq_to_string(keysetseq: Vec<KeySet>) -> String {
    let mut v_keyset_str: Vec<String> = vec![];
    for keyset in keysetseq {
        v_keyset_str.append(&mut vec![keyset.to_string()]);
    }
    v_keyset_str.join(",")
}

#[cfg(test)]
mod tests {
    use super::*;
    use control::Key;

    #[test]
    fn test_set_key_has_key() {
        let mut ks = KeySet::new();
        assert!(!ks.has_key(Key::Up));
        assert!(!ks.has_key(Key::Right));
        assert!(!ks.has_key(Key::Left));
        assert!(!ks.has_key(Key::Down));
        assert!(!ks.has_key(Key::RightTurn));
        assert!(!ks.has_key(Key::LeftTurn));
        assert!(!ks.has_key(Key::Start));

        ks.set_key(Key::Up);
        ks.set_key(Key::Right);
        assert!(ks.has_key(Key::Up));
        assert!(ks.has_key(Key::Right));
        assert!(!ks.has_key(Key::Left));
        assert!(!ks.has_key(Key::Down));
        assert!(!ks.has_key(Key::RightTurn));
        assert!(!ks.has_key(Key::LeftTurn));
        assert!(!ks.has_key(Key::Start));
    }

    #[test]
    fn test_parse_keysetseq_1() {
        let expected: &[KeySet] = &[
            KeySet::from_key(Key::Right),
            KeySet::from_key(Key::Left),
            KeySet::from_key(Key::Down),
            KeySet::from_key(Key::Up),
            KeySet::from_key(Key::RightTurn),
            KeySet::from_key(Key::LeftTurn),
            KeySet::from_key(Key::Start),
        ];

        assert_eq!(
            expected,
            parse_keysetseq(">,<,v,^,A,B,S").unwrap().as_slice()
        );
    }

    #[test]
    fn test_parse_keysetseq_2() {
        let expected: &[KeySet] = &[
            KeySet::from_keys(&[Key::Right, Key::RightTurn]),
            KeySet::from_keys(&[Key::RightTurn, Key::Right]),
            KeySet::from_keys(&[Key::Left, Key::LeftTurn]),
            KeySet::from_keys(&[Key::LeftTurn, Key::Left]),
            KeySet::from_keys(&[Key::Down, Key::RightTurn]),
            KeySet::from_keys(&[Key::Down, Key::LeftTurn]),
        ];

        assert_eq!(
            expected,
            parse_keysetseq(">A,>A,<B,<B,vA,vB").unwrap().as_slice()
        );
    }

    #[test]
    fn test_constructor() {
        assert_eq!(KeySet::new().keys, 0);
        assert_eq!(KeySet::from_key(Key::Up).keys, 1);
        assert_eq!(KeySet::from_key(Key::Right).keys, 2);
        assert_eq!(KeySet::from_key(Key::Down).keys, 4);
        assert_eq!(KeySet::from_key(Key::Left).keys, 8);
        assert_eq!(KeySet::from_key(Key::RightTurn).keys, 16);
        assert_eq!(KeySet::from_key(Key::LeftTurn).keys, 32);
        assert_eq!(KeySet::from_key(Key::Start).keys, 64);
        assert_eq!(KeySet::from_keys(&[Key::Left, Key::RightTurn]).keys, 24);
        assert_eq!(KeySet::from_keys(&[Key::Right, Key::LeftTurn]).keys, 34);
    }

    #[test]
    fn test_has_some_key() {
        let ks_1 = KeySet::from_keys(&[Key::Left, Key::RightTurn]);
        assert!(ks_1.has_turn_key());
        assert!(ks_1.has_arrow_key());

        let ks_2 = KeySet::from_key(Key::Left);
        assert!(!ks_2.has_turn_key());
        assert!(ks_2.has_arrow_key());

        let ks_3 = KeySet::from_key(Key::RightTurn);
        assert!(ks_3.has_turn_key());
        assert!(!ks_3.has_arrow_key());

        let ks_4 = KeySet::from_key(Key::Start);
        assert!(!ks_4.has_turn_key());
        assert!(!ks_4.has_arrow_key());
    }

    #[test]
    fn test_to_string() {
        assert_eq!(KeySet::from_key(Key::Down).to_string(), "v");
        assert_eq!(
            KeySet::from_keys(&[Key::Left, Key::RightTurn]).to_string(),
            "<A"
        );
        assert_eq!(
            KeySet::from_keys(&[Key::Right, Key::Down, Key::LeftTurn]).to_string(),
            ">vB"
        );
    }
}
