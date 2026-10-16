# Late-source reconciliation and the preferred purity-cut proof

The repository advanced during preparation of this report. Batch 144
source 08, `zfc_one_schema_research.zip`, arrived in commit
`39409c8c921cccdbd6162c8767c84cfb7df65df1`. Its mathematical calibration of
equality-free subset-seeded PSC alone was subsequently accepted in
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-144-source-08.md`.
The updated `raw_psc.md` explicitly credits this result. Commit
`45a1b47c4d742b74def38121388509985a907d25` adds semantic Lean lemmas in
`PSCSaturation.lean`; the inspected late-tree pin is
`bda2b4860e6b3664d8ae84978bd7683572f55f49`.

Accordingly, equality-free PSC-only equiconsistency and hereditary
saturation are not claimed as newly discovered results of the present
report. The report supplies an independently checked alternative bootstrap
using incoming-profile fragments and a nonempty monochromatic decoder.
Source 08 instead bootstraps with equivalence of both incoming and outgoing
profiles. Both routes give raw transitive covers, Separation and Union.

The preferred final H-closure argument is source 08's purity cut, which is
shorter than the least-transitive-cover construction in the earlier working
proof. Define D as incoming-profile equivalence,

    S(a) := all D-copies of members of a are themselves members of a,
    H(a) := S(a) and a has a raw transitive cover whose members are S.

Directly from this definition H is D-invariant and hereditary. Assume
S(B) and that every raw member of B is H. Choose one raw transitive cover
V with B ⊆ V. Raw Separation supplies

    W = {u in V : H(u)}.

Every member of B belongs to W. If x belongs to W and y belongs to x,
transitivity of V gives y in V, and heredity of H gives H(y); hence y
belongs to W. Therefore W is transitive. Every member of W is H and thus
S. This W witnesses H(B).

No selection of a family of covers, no least transitive cover, and no
coextensional-functional Replacement are needed for this lemma. Saturation
of V or W is unnecessary. There is no circularity: heredity follows from
the original first-order definition of H before the closure lemma is used.

The final mathematical chapter `sections/theory.tex` uses this purity-cut
proof and credits source 08. Its separate exact-local-image theorem remains
in place for the direct proof of interpreted Replacement. The finite
regressions for the incoming-profile monochromatic decoder remain distinct
evidence for that alternative bootstrap; they are not finite models of PSC.

Source 08 transfers the entire extensional PSC schema by guarding the raw
matrix with H on inputs and outputs and saturating the raw hull under D.
The present chapter instead proves the individual interpreted ZF axioms,
including direct Infinity. These are alternative ordinary mathematical
routes to the same calibrated theory. Neither route certifies the frozen
252-state CP/GIC experiment or a new literal machine endpoint.
