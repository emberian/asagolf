//! `ProofSize`: a number type for counting fully-expanded proof trees.
//!
//! The thing we count (the cut-free proof tree) is astronomically large, but its
//! *cardinality* is just an integer. Lemma inlining alone is single-exponential,
//! so the count is an exact bignum of at most ~1e6 digits — cheap. Genuine
//! quantifier cut-elimination is non-elementary (a tower of exponentials); for
//! that regime we fall back to tracking log10, then log10 log10.
//!
//! Variants, in order of magnitude:
//!   Exact(n)            n itself (used while digit-count is sane)
//!   Big   { lg }        value = 10^lg            (lg = log10 value, f64)
//!   Huge  { lglg }      value = 10^(10^lglg)     (non-elementary regime)

use num_bigint::BigUint;
use num_traits::{One, Zero};

/// Switch Exact -> Big once the integer exceeds this many decimal digits.
/// Below this, exact arithmetic is fast and we keep full precision.
const EXACT_DIGIT_CAP: u64 = 40_000;

#[derive(Clone, Debug)]
pub enum ProofSize {
    Exact(BigUint),
    Big { lg: f64 },     // 10^lg
    Huge { lglg: f64 },  // 10^(10^lglg)
}

impl ProofSize {
    pub fn zero() -> Self {
        ProofSize::Exact(BigUint::zero())
    }
    pub fn one() -> Self {
        ProofSize::Exact(BigUint::one())
    }
    pub fn from_u64(v: u64) -> Self {
        ProofSize::Exact(BigUint::from(v))
    }

    /// Approximate log10 of the value (used internally + for display).
    pub fn log10(&self) -> f64 {
        match self {
            ProofSize::Exact(n) => {
                if n.is_zero() {
                    f64::NEG_INFINITY
                } else {
                    // log10(n) = (#bits - 1 + frac) * log10(2), via the top bits.
                    let bits = n.bits();
                    // Take the leading 64 bits for a precise mantissa.
                    let shift = bits.saturating_sub(64);
                    let top: u64 = (n >> shift).to_u64_digits().first().copied().unwrap_or(0);
                    let mantissa = (top as f64).log2() + shift as f64;
                    mantissa * std::f64::consts::LOG10_2
                }
            }
            ProofSize::Big { lg } => *lg,
            ProofSize::Huge { lglg } => 10f64.powf(*lglg),
        }
    }

    fn normalize(self) -> Self {
        match self {
            ProofSize::Exact(ref n) if n.bits() as u64 > EXACT_DIGIT_CAP * 4 => {
                let lg = self.log10();
                ProofSize::from_lg(lg)
            }
            other => other,
        }
    }

    fn from_lg(lg: f64) -> Self {
        if lg.is_finite() && lg.abs() < 1e300 {
            ProofSize::Big { lg }
        } else {
            // log10 itself overflowed f64 range -> non-elementary tower.
            ProofSize::Huge {
                lglg: if lg > 0.0 { lg.log10() } else { f64::NEG_INFINITY },
            }
        }
    }

    /// self + other
    pub fn add(&self, other: &ProofSize) -> ProofSize {
        if let (ProofSize::Exact(a), ProofSize::Exact(b)) = (self, other) {
            return ProofSize::Exact(a + b).normalize();
        }
        // log-space: log10(10^x + 10^y) = max + log10(1 + 10^-|x-y|)
        let (x, y) = (self.log10(), other.log10());
        if !x.is_finite() {
            return other.clone();
        }
        if !y.is_finite() {
            return self.clone();
        }
        let (hi, lo) = if x >= y { (x, y) } else { (y, x) };
        let lg = hi + (1.0 + 10f64.powf(lo - hi)).log10();
        ProofSize::from_lg(lg)
    }

    /// self * small integer multiplicity
    pub fn mul_u64(&self, m: u64) -> ProofSize {
        if m == 0 {
            return ProofSize::zero();
        }
        match self {
            ProofSize::Exact(n) => ProofSize::Exact(n * BigUint::from(m)).normalize(),
            _ => ProofSize::from_lg(self.log10() + (m as f64).log10()),
        }
    }

    /// self * other (full multiply; used for compounding factors)
    pub fn mul(&self, other: &ProofSize) -> ProofSize {
        if let (ProofSize::Exact(a), ProofSize::Exact(b)) = (self, other) {
            return ProofSize::Exact(a * b).normalize();
        }
        ProofSize::from_lg(self.log10() + other.log10())
    }

    /// Human-readable "≈10^N" / exact for small values.
    pub fn pretty(&self) -> String {
        match self {
            ProofSize::Exact(n) => {
                let digits = self.log10();
                if digits < 18.0 {
                    n.to_string()
                } else {
                    format!("≈10^{:.1}  ({} digits)", digits, digits.floor() as i128 + 1)
                }
            }
            ProofSize::Big { lg } => format!("≈10^{:.3e}  ({:.0} digits)", lg, lg.floor() + 1.0),
            ProofSize::Huge { lglg } => format!("≈10^(10^{:.3})  [non-elementary]", lglg),
        }
    }
}
