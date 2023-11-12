use crate::Random;

impl Random {
    pub fn next_ascii96(&mut self) -> u8 {
        let b = (self.next_f64() * 96.0).trunc() as u8;
        if b < 95 {
            b + b' '
        } else {
            b'\n'
        }
    }
}

#[cfg(test)]
const ASCII96_RANGES: [u64; 97] = [
    0x00000000000000,
    0x00555555555556,
    0x00aaaaaaaaaaab,
    0x01000000000000,
    0x01555555555556,
    0x01aaaaaaaaaaab,
    0x02000000000000,
    0x02555555555556,
    0x02aaaaaaaaaaab,
    0x03000000000000,
    0x03555555555556,
    0x03aaaaaaaaaaab,
    0x04000000000000,
    0x04555555555556,
    0x04aaaaaaaaaaab,
    0x05000000000000,
    0x05555555555556,
    0x05aaaaaaaaaaab,
    0x06000000000000,
    0x06555555555556,
    0x06aaaaaaaaaaab,
    0x07000000000000,
    0x07555555555556,
    0x07aaaaaaaaaaab,
    0x08000000000000,
    0x08555555555556,
    0x08aaaaaaaaaaab,
    0x09000000000000,
    0x09555555555556,
    0x09aaaaaaaaaaab,
    0x0a000000000000,
    0x0a555555555556,
    0x0aaaaaaaaaaaab,
    0x0b000000000000,
    0x0b555555555555,
    0x0baaaaaaaaaaab,
    0x0c000000000000,
    0x0c555555555555,
    0x0caaaaaaaaaaab,
    0x0d000000000000,
    0x0d555555555555,
    0x0daaaaaaaaaaab,
    0x0e000000000000,
    0x0e555555555555,
    0x0eaaaaaaaaaaab,
    0x0f000000000000,
    0x0f555555555555,
    0x0faaaaaaaaaaab,
    0x10000000000000,
    0x10555555555555,
    0x10aaaaaaaaaaab,
    0x11000000000000,
    0x11555555555555,
    0x11aaaaaaaaaaab,
    0x12000000000000,
    0x12555555555555,
    0x12aaaaaaaaaaab,
    0x13000000000000,
    0x13555555555555,
    0x13aaaaaaaaaaab,
    0x14000000000000,
    0x14555555555555,
    0x14aaaaaaaaaaab,
    0x15000000000000,
    0x15555555555555,
    0x15aaaaaaaaaaaa,
    0x16000000000000,
    0x16555555555555,
    0x16aaaaaaaaaaaa,
    0x17000000000000,
    0x17555555555555,
    0x17aaaaaaaaaaaa,
    0x18000000000000,
    0x18555555555555,
    0x18aaaaaaaaaaaa,
    0x19000000000000,
    0x19555555555555,
    0x19aaaaaaaaaaaa,
    0x1a000000000000,
    0x1a555555555555,
    0x1aaaaaaaaaaaaa,
    0x1b000000000000,
    0x1b555555555555,
    0x1baaaaaaaaaaaa,
    0x1c000000000000,
    0x1c555555555555,
    0x1caaaaaaaaaaaa,
    0x1d000000000000,
    0x1d555555555555,
    0x1daaaaaaaaaaaa,
    0x1e000000000000,
    0x1e555555555555,
    0x1eaaaaaaaaaaaa,
    0x1f000000000000,
    0x1f555555555555,
    0x1faaaaaaaaaaaa,
    0x20000000000000,
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verify_ascii96_ranges() {
        for i in 0..96 {
            assert_eq!(ascii96_from_u53(ASCII96_RANGES[i]), i as u8);
            assert_eq!(ascii96_from_u53(ASCII96_RANGES[i + 1] - 1), i as u8);
        }
    }

    #[test]
    fn search_ascii96_ranges() {
        println!("0 -> {}", ascii96_from_u53(0));
        for target in 0u8..96 {
            let min = binary_search_range(|x| ascii96_from_u53(x) < target);
            if min != 0 {
                assert_eq!(ascii96_from_u53(min - 1), target - 1);
            }
            println!("{min:#x}.. -> {target}");
        }
        println!(
            "{:#x} -> {}",
            (1u64 << 53) - 1,
            ascii96_from_u53((1 << 53) - 1)
        );
    }

    fn ascii96_from_u53(x: u64) -> u8 {
        assert!(x < 1 << 53);
        let hi = (x >> 26) as f64;
        let lo = (x & ((1 << 26) - 1)) as f64;
        let f = (hi * 67108864.0 + lo) * (1.0 / 9007199254740992.0);
        let c = (f * 96.0).trunc();
        assert!(0.0 <= c && c < 96.0 && (0..96).contains(&(c as u8)));
        c as u8
    }

    fn binary_search_range<F: FnMut(u64) -> bool>(mut less: F) -> u64 {
        let mut lo = 0u64;
        let mut hi = 1u64 << 53;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if less(mid) {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo
    }
}
