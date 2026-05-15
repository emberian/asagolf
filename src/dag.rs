//! The proof DAG and its symbolic (never-materialized) expansion.
//!
//! A lemma's proof is a list of primitive inference steps plus references to
//! other lemmas. The fully-inlined ("cut-free") proof is the tree you'd get by
//! recursively substituting every lemma reference with its own subproof. We
//! never build that tree; we fold two metrics bottom-up over the DAG:
//!
//!   nodes(T) = local_steps(T) + Σ  mult · nodes(ref)        [proof steps]
//!   bits(T)  = stmt_syms(T)·local_steps(T)
//!              + Σ mult · bits(ref) · growth                 [written length]
//!
//! `growth` (≥1) models substitution duplicating terms each time a lemma is
//! inlined into a larger context — the reason bitlength outruns node count.

use crate::number::ProofSize;

pub type LemmaId = usize;

#[derive(Clone, Debug)]
pub struct Lemma {
    pub name: String,
    /// Primitive inference steps in *this* proof that are NOT lemma calls
    /// (axiom instantiations, modus ponens, generalization, ...).
    pub local_steps: u64,
    /// Symbol count of this lemma's *statement* (the formula at its root node).
    pub stmt_syms: u64,
    /// Per-inline term-duplication factor for the bitlength metric (≥ 1.0).
    pub growth: f64,
    /// (referenced lemma, how many times it is invoked in this proof).
    pub refs: Vec<(LemmaId, u64)>,
}

#[derive(Default)]
pub struct Dag {
    pub lemmas: Vec<Lemma>,
}

#[derive(Clone)]
pub struct Expansion {
    pub nodes: ProofSize,
    pub bits: ProofSize,
}

impl Dag {
    pub fn add(
        &mut self,
        name: &str,
        local_steps: u64,
        stmt_syms: u64,
        growth: f64,
        refs: Vec<(LemmaId, u64)>,
    ) -> LemmaId {
        // Acyclicity invariant: a lemma may only reference earlier ids.
        for (r, _) in &refs {
            assert!(*r < self.lemmas.len(), "{name}: forward/cyclic ref to {r}");
        }
        self.lemmas.push(Lemma {
            name: name.to_string(),
            local_steps,
            stmt_syms,
            growth,
            refs,
        });
        self.lemmas.len() - 1
    }

    pub fn id(&self, name: &str) -> LemmaId {
        self.lemmas
            .iter()
            .position(|l| l.name == name)
            .unwrap_or_else(|| panic!("unknown lemma {name}"))
    }

    /// Bottom-up fold (ids are in topological order by construction).
    pub fn expand(&self) -> Vec<Expansion> {
        let mut out: Vec<Expansion> = Vec::with_capacity(self.lemmas.len());
        for l in &self.lemmas {
            let mut nodes = ProofSize::from_u64(l.local_steps);
            let mut bits =
                ProofSize::from_u64(l.stmt_syms.saturating_mul(l.local_steps.max(1)));
            for &(r, mult) in &l.refs {
                let e = &out[r];
                nodes = nodes.add(&e.nodes.mul_u64(mult));
                let grown = if (l.growth - 1.0).abs() < 1e-12 {
                    e.bits.clone()
                } else {
                    e.bits.mul(&ProofSize::Big {
                        lg: l.growth.log10(),
                    })
                };
                bits = bits.add(&grown.mul_u64(mult));
            }
            out.push(Expansion { nodes, bits });
        }
        out
    }
}
