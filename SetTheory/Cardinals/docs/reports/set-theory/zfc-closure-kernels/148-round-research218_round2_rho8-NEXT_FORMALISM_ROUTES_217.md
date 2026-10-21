# Formalism routes toward 217 states: analytic triage

Date: 2026-10-20. No new machine, source-size bound, or formula enumeration is claimed here. The physical-state target is 217 or fewer; a logical variation is useful only if its exact source can improve on the published 205-subtree construction or permit cheaper compiled roles.

## Ruled out or newly constrained

1. Every fixed membership orientation is ZFC-provably consistent; the independent review is `UPSTREAM_FIXED_ORIENTATION_CLOSURE_REVIEW.md`.
2. The union of all six orientations is also covered by a new mixed-J/D invariant; see `MIXED_ORIENTATION_UNION_OBSTRUCTION.md`. The new extension has an independent ordinary-proof PASS in `../research217_theory_review/MIXED_ORIENTATION_UNION_INDEPENDENT_REVIEW.md`; no proof-assistant build is claimed.
3. An always implication-headed fourth builder, such as `U=I(b,c)`, is also too weak by the existing full-HC model. In that matrix, implication outputs only values 0,1,3, and every failure of unrestricted L requires U=2. Thus all such restricted rows are valid simultaneously, with every retained row and the exact full seed. Q-headed fourth builders likewise take only 0 or 3 there. Merely deleting the +1 membership tag to make an implication code does not escape this obstruction.

The previous full-HC model is documented at `../latest219_baseline/reports/140-k219-res-theory-restricted_rho8_strong_countermodel.md`; our fixed finite matrix checks and exact native counterexamples are in `bootstrap_gap_receipt.json` and `SYNTACTIC_GAP.md`.

## U=F together with U=R(b,c): now ruled out

A stronger invariant has now closed this route. `ALL_MEMBERSHIP_FOURTH_OBSTRUCTION.md` proves in ZFC the consistency of the enlarged calculus permitting EVERY membership-headed fourth code, with independent labels and the full seed. It therefore covers F+Rbc, all six orientations, all their unions, and every always-membership-headed code builder. The independent reviewer returned PASS at SHA256 `1525871efd5611ddf13d77f8b8fafb975ff1cf24065134dec9c7f77034a1dd39`, including the new quantified-monotonicity exclusion and raw truth0 case. No proof-assistant endpoint is claimed.

The historical observation below explains why the earlier identity-enlarged invariant did not suffice. The successful stronger invariant does NOT add identities. In fact it proves that no theorem has an R-headed immediate implication antecedent, so the suggested relative truth code I(F,F) is not derivable.

A necessary caution: the old HC model *validates* K, explosion, and DNE. That does not mean those laws were proved from its U=F axiom family. They cannot be seeded as theorems of this new union without certificates.

There is a concrete reason the old auxiliary class fails unchanged. Let `t=I(F,F)` and `p(c)=I(c,F)`. If identities are freely admitted in an auxiliary overapproximation, H_F(p(c),b,c) detaches to

`J_F(b,c)=I(I(p(c),c),I(b,c))`.

The formula J_F(F,F) is exactly `I(I(t,F),t)`, so it is the required minor for J_F(b,t). Their MP yields `I(b,t)` for every b. Thus J_F majors are no longer inert. This is a valid detachment inside that identity-enlarged invariant; it is not a claimed derivation in the original union, whose unrestricted identities have not yet been established.

That auxiliary observation gave no K/S, no `I(b,0)` for native truth 0, and no specialization bridge. The new full-seed invariant supplies the negative conclusion without a semantic representation. The earlier fresh-diagonal Heyting argument remains conditional on a representation premise and does not conflict with this syntactic obstruction.

Implementing this union would emit a second row or require a selector between two fourth builders. No source saving is known. Source-cost plausibility should be checked before a formula search.

## Raw Cantor fourth code P(b,c)

This differs materially from both R(b,c) and I(b,c). P is the raw pairing integer, without the multiplication by four or tag addition. It can have any constructor residue, including quantifier, equality, and membership tags, and `P(0,0)=0`.

Accordingly the membership-only invariant's tag exclusions and strict growth at zero fail. The full-HC argument for implication/Q-headed fourth values also does not apply. These failures of old obstructions are not a positive calibration result.

The easy upper consistency direction again follows from literal rho8 inclusion. No reverse translation, complete basis proof, or full-seed countermodel is presently supplied. Exact arithmetic code equalities would have to be handled, not arbitrary formula substitution. A source-only question has been sent to the encoding lane: whether a raw pair operation already exists in a reusable form and can plausibly lower the 205-subtree count. No new decoder or count is assumed.

## A calibrated three-input alternative: K, S, and Peirce

Replace rho8 with the three exact native schemas

`K(a,b)=I(a,I(b,a))`,

`S(a,b,c)=I(I(a,I(b,c)),I(I(a,b),I(a,c)))`,

`Prc(a,b)=I(I(I(a,b),a),a)`.

Keep every other native row, raw truth, MP, GEN, and the full seed bundle. This has a uniform theorem translation in both directions, unlike the unresolved alternatives above.

From unrestricted rho8, the pinned `CD230.v` gives K as cd16, Peirce as cd25, and S as cd106. Those are schemas over arbitrary literal natural codes, so their finite proofs transfer directly.

Conversely, write `h=(C→U)→A` and `k=A→C`. Under assumptions h,k and an additional temporary assumption `C→U`, two MPs give A and then C. The propositional deduction theorem justified by K/S yields `(C→U)→C` under h,k. Peirce at C,U gives C. K then gives `B→C`. Discharging k and h using the same K/S deduction theorem yields exactly

`((C→U)→A)→((A→C)→(B→C))`.

No GEN occurs in this deduction, so there is no hidden quantified-assumption side condition. The finite K/S deduction transformation works for every raw code, including native zero aliases. It therefore uniformly replaces every original rho8 leaf and establishes exact theorem equivalence, hence consistency equivalence, while retaining the seed and all native quantifier machinery.

The open question is exclusively implementation cost. Three rows may cost more than the eliminated fourth-input parser. Their expression trees use eleven implication occurrences before cross-row sharing, compared with six in L; they also require two additional stack pushes. Conversely they use only the existing three fields and reuse the existing implication macro. Occurrence counts do not determine subtree count or physical state count. The encoding lane has been asked for structural assessment before any compilation/search. Until that assessment, this is a calibrated formalism option, not a 217-state candidate.

## Subsequent source-cost evidence

The encoding lane found an existing inert three-row source experiment at `../latest219_baseline/source140/research/experiments/receipts/three_row_proposition/summary.json`. Its recorded best KSP count is 216 DAG nodes across 3888 association/order/renaming cases, with KBP at 214 and KSD at 216. I read that receipt but did not execute the received search. It makes KSP a poor compactness prospect under those templates, not an impossibility theorem.

The raw P macro can reuse the existing implication constructor's stack-pop and pairing core, replacing its scale-by-four loop with a one-increment loop; the encoding lane identifies a 24-leaf version. It is not already a complete source subtree. The exact raw `1*P+0` choice was skipped by the old pair-binder experiment. No <205 count follows without literal source pricing.


## Newly calibrated alternatives and cost boundary

The two-row H/PW basis has a complete exact native theorem-equivalence proof, with independent replay of its ten-step K/Peirce bootstrap and all 97 rows of the H/K/Peirce-to-S bridge. See `../research217_native_basis_review/NATIVE_CALIBRATION.md`. The adjacent `THREE_FIELD_ENUMERATOR_BRIDGE.md` also proves finite-proof compilation, exact two-row stack bookkeeping, three-field command recoding, and cofinal reset prefixes for the ORIGINAL draining scheduler. Neither theorem automatically verifies an edited source or table. The source lane's literal templates are noncompetitive: best row-separated no-reader family 209 DAG nodes and a further association diagnostic 207, both above the current 205 baseline.

A qualitatively different calibrated route is replacing the pairing codec everywhere in the formula constructors by S(a,b)=2^a(2b+1)-1. `../research217_codec_pairing/CODEC_ISOMORPHISM.md` gives a bijective simultaneous permutation of formula codes and raw labels, preserving every native row, the complete code-as-label seed, and F=1. This transfers the exact theorem relation and consistency. It does NOT transport raw proof-list pairing or additive counters through that permutation, and does not inherit old scheduler residue results. Pair/unpair macros, full source cost, finite-command compilation and machine runtime remain separate obligations. No state saving is yet known.

## Subsequent genuinely mixed-tag test: also closed negatively

The union U=R(b,c) OR U=I(b,c) lies outside both earlier separate obstructions, but a new correlated invariant settles it. `../research217_mixed_tag_basis/MIXED_R_I_OBSTRUCTION.md` has independent ordinary-proof PASS at SHA256 `c4186c5ce28910a4595b0a18b483134c0b80e83e522fbf709e4e5d160e9da1f3`. The full seed is retained. The mixed calculus does derive I(F,0)=4 by a seven-node native certificate, but its H/H consequence families close after adding only this exception. No other R-antecedent implication is derivable, so F→F and K(F,b) are absent. This closes the exact Rbc/Ibc proposal without a CD search; it does not rule out other mixed-tag correlations.
