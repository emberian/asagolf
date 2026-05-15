//! The Birkhoff-ASA → ℝ-substrate → ZFC/FOL proof model.
//!
//! ⚠️  PRE-CALIBRATION. The per-lemma `local_steps` / fanout / multiplicity
//! constants below are *structurally* principled (depth and reuse patterns
//! reflect how each layer actually decomposes) but their magnitudes are
//! placeholders until step 2 regression-fits them to real `set.mm` lemma
//! statistics. The deliverable right now is the machinery + the gap structure,
//! not the digits.

use crate::dag::{Dag, LemmaId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Foundation {
    /// Ordered-field axioms added. ASA-minimal: no ℝ construction, no
    /// completeness. The honest floor.
    F0OrderedField,
    /// F0 + closure under √ of nonnegatives (needed iff length/angle
    /// constructions take roots). Still added axioms.
    F1EuclideanField,
    /// Constructive Cauchy reals *built* in ZFC (ℕ→ℤ→ℚ→Cauchy w/ modulus),
    /// ordered field proven. NO completeness.
    F2ConstructiveReals,
    /// Classical Dedekind reals + least-upper-bound completeness proven in
    /// ZFC. "All of real analysis" — the strawman.
    F3DedekindReals,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kernel {
    /// Metamath-style condensed detachment: one logic step ≈ one primitive.
    /// Matches set.mm, our calibration substrate.
    MetamathCD,
    /// Raw Hilbert system: every CD step expands into an axiom-schema
    /// instantiation chain + modus ponens. A large per-step multiplier.
    RawHilbert,
}

impl Kernel {
    /// Primitive inferences per "one logic step" at this granularity.
    fn unit_cost(self) -> u64 {
        match self {
            Kernel::MetamathCD => 1,
            // A CD step = unify + MP; raw Hilbert reconstructs the unifier via
            // a chain of substitution-axiom instantiations. Order ~tens.
            Kernel::RawHilbert => 35,
        }
    }
}

pub struct Built {
    pub dag: Dag,
    pub asa: LemmaId,
    pub real_substrate: LemmaId,
}

/// Build the full DAG for a (foundation, kernel) configuration and return the
/// ASA lemma id plus the ℝ-substrate root (so the report can attribute mass).
pub fn build(found: Foundation, kernel: Kernel) -> Built {
    let mut d = Dag::default();
    let u = kernel.unit_cost();

    // ---- FOL/ZFC kernel leaf -------------------------------------------------
    // One "logic unit": the cost of a single discharged logical inference at
    // the chosen kernel granularity. Everything bottoms out here.
    let logic = d.add("logic_unit", u, 6, 1.0, vec![]);

    // ZFC set-theoretic plumbing reused everywhere (pair/union/separation
    // instances, extensionality rewrites). Modest fanout over `logic`.
    let zfc = d.add("zfc_plumbing", 4 * u, 12, 1.05, vec![(logic, 9)]);

    // ---- ℝ substrate ladder --------------------------------------------------
    let real_substrate = build_real_substrate(&mut d, found, logic, zfc);

    // ---- Birkhoff geometry layer (shared across foundations) ----------------
    // The 4 postulates must reference the substrate even to be *stated*.
    let p_line = d.add("post_line_unique", 3 * u, 14, 1.1, vec![(real_substrate, 1)]);
    let p_ruler = d.add("post_ruler", 5 * u, 22, 1.1, vec![(real_substrate, 2)]);
    let p_prot = d.add("post_protractor", 6 * u, 26, 1.1, vec![(real_substrate, 2)]);
    let p_sas = d.add("post_sas_similarity", 7 * u, 30, 1.1, vec![(real_substrate, 3)]);

    // Derived geometry lemmas. Betweenness is *defined* via distance additivity
    // (the Birkhoff bookkeeping win): no Pasch/collinearity case explosion.
    let betw = d.add(
        "betweenness_via_dist",
        8 * u,
        20,
        1.15,
        vec![(real_substrate, 2), (p_ruler, 2)],
    );
    let ray = d.add(
        "ray_coordinatization",
        9 * u,
        24,
        1.15,
        vec![(p_ruler, 2), (p_prot, 2), (betw, 1)],
    );
    let seg_copy = d.add(
        "segment_copy_unique",
        7 * u,
        18,
        1.15,
        vec![(p_ruler, 2), (betw, 1)],
    );
    let ang_copy = d.add(
        "angle_copy_unique",
        9 * u,
        22,
        1.2,
        vec![(p_prot, 2), (ray, 2)],
    );
    let nondegen = d.add(
        "triangle_nondegeneracy",
        5 * u,
        16,
        1.1,
        vec![(p_line, 1), (betw, 1)],
    );

    // ASA: copy the included side and the two angles, hit the SAS/similarity
    // postulate, conclude congruence via uniqueness of the ray maps.
    let asa = d.add(
        "ASA",
        12 * u,
        40,
        1.25,
        vec![
            (seg_copy, 2),
            (ang_copy, 2),
            (ray, 2),
            (nondegen, 1),
            (p_sas, 1),
        ],
    );

    Built {
        dag: d,
        asa,
        real_substrate,
    }
}

/// The swappable foundation. Returns the id of `real_substrate`: the single
/// lemma "the number structure ASA needs is available", which the geometry
/// layer depends on.
fn build_real_substrate(
    d: &mut Dag,
    found: Foundation,
    logic: LemmaId,
    zfc: LemmaId,
) -> LemmaId {
    match found {
        Foundation::F0OrderedField => {
            // Just the ordered-field axioms, added. A handful of axiom lemmas
            // glued by order/field rewrites. Shallow, tiny.
            let field = d.add("ordered_field_axioms", 6, 10, 1.02, vec![(logic, 4)]);
            d.add("real_substrate", 3, 8, 1.02, vec![(field, 1), (zfc, 1)])
        }
        Foundation::F1EuclideanField => {
            let field = d.add("ordered_field_axioms", 6, 10, 1.02, vec![(logic, 4)]);
            let sqrt = d.add(
                "sqrt_closure",
                10,
                14,
                1.05,
                vec![(field, 2), (logic, 6)],
            );
            d.add(
                "real_substrate",
                3,
                8,
                1.03,
                vec![(field, 1), (sqrt, 1), (zfc, 1)],
            )
        }
        Foundation::F2ConstructiveReals => {
            // ℕ → ℤ → ℚ → Cauchy-with-modulus, ordered field proven.
            // Deep chain, moderate reuse, NO completeness.
            let nat = d.add("nat_in_zfc", 30, 18, 1.1, vec![(zfc, 6), (logic, 12)]);
            let int = d.add("int_from_nat", 40, 22, 1.12, vec![(nat, 3), (zfc, 4)]);
            let rat = d.add("rat_from_int", 55, 26, 1.12, vec![(int, 4), (nat, 2)]);
            let cauchy = d.add(
                "cauchy_seq_with_modulus",
                90,
                34,
                1.18,
                vec![(rat, 6), (nat, 4), (zfc, 5)],
            );
            let field = d.add(
                "constructive_ordered_field",
                130,
                40,
                1.2,
                vec![(cauchy, 8), (rat, 5)],
            );
            d.add(
                "real_substrate",
                12,
                12,
                1.1,
                vec![(field, 1), (zfc, 1)],
            )
        }
        Foundation::F3DedekindReals => {
            // Same construction scale + the heavy part: LUB completeness over
            // arbitrary bounded sets (powerset-driven, high reuse).
            let nat = d.add("nat_in_zfc", 30, 18, 1.1, vec![(zfc, 6), (logic, 12)]);
            let int = d.add("int_from_nat", 40, 22, 1.12, vec![(nat, 3), (zfc, 4)]);
            let rat = d.add("rat_from_int", 55, 26, 1.12, vec![(int, 4), (nat, 2)]);
            let cut = d.add(
                "dedekind_cut",
                80,
                32,
                1.18,
                vec![(rat, 6), (zfc, 6)],
            );
            let field = d.add(
                "dedekind_ordered_field",
                140,
                42,
                1.22,
                vec![(cut, 8), (rat, 5)],
            );
            // Completeness: every nonempty bounded-above set has a sup. This is
            // the mass center — powerset comprehension + cut arithmetic, reused
            // heavily downstream.
            let lub = d.add(
                "lub_completeness",
                260,
                52,
                1.3,
                vec![(cut, 14), (field, 6), (zfc, 10)],
            );
            d.add(
                "real_substrate",
                15,
                14,
                1.15,
                vec![(field, 1), (lub, 1), (zfc, 1)],
            )
        }
    }
}
