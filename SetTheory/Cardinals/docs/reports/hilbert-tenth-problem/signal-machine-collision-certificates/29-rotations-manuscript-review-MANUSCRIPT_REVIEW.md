# Independent manuscript review of Report 59

4 October 2026. Final verdict: **PASS**, within the conventional mathematical, inert-source, exact-algebra and rendered-document scope described below. No blocking mathematical or visual defect remains.

## Final source and PDF bindings

The verdict binds the release at `/workspace/shared/five-signal-rotation-family59-release-20261004`:

- `manuscript/report59.tex`: `3473c1fe22ecbfe55fd2728c9d243c166677811e3738e241dee8f2ff88ed8c66`
- `Report59.pdf`: `a5fb0f18f1d60efb6d6ba2c884434a719ccae488b6dc89aebdbfbff5b4201fb0`
- `manuscript/fixture-table.tex`: `d3ce355756c41d21966cac575c8f98afabac56e81c91c37512e4fe871e07bf2e`
- `manuscript/geometry-figure.tex`: `3fdb9ee48c04fa0e5217cc775c8c8e10f68f9cb70252bd7b6877674f931ead59`

The PDF has 22 Letter-size pages, comprising the title page and printed pages 1–21. `RENDER_BINDING.json` supplies all final page hashes. The final TeX and independently extracted PDF text are preserved locally in this review directory.

The initial reviewed source was `941a0deb94d7b59ba9ff4ee0f81793b63633aa2899b6bebaca9c0a5bf76344a3`; its PDF was `0cb46f9a78c2dbb84890c794d90535aed46576d64f5834af3bc7cf631e7ee713`. The four-paragraph difference from that exact source is recorded in `SOURCE_CHANGES.diff`. Reversing precisely those changes in the final source reproduces the initial SHA-256, so the saved initial-source reconstruction is byte-verified, rather than an assumed draft.

## Scope and independence

I read the complete 703-line manuscript, its two included TeX files, the frozen family proof, the complete 158-line physical constructor as inert text, the family independent audit and arithmetic audit, the complete real-input companion, its source notes and its independent audit. I inspected the relevant constructive statements and proofs of `Pell.matiyasevic` and `Pell.eq_pow_of_pell` in the pinned Lean source without executing Lean.

The principal frozen mathematical bindings are:

- Family `PROOF.md`: `14c3d694d9e0c21f3ad3b125c0d1f2bbf47793e1283c9314aa3855ef60c89fc5`
- Family `static_family.py`: `c6ce6ae3873da154c4b7f200f762408f36583d20e424ac6fca4661bd0bd9ce41`
- Family `PACKET_MANIFEST.json`: `646de47472089e9909fafbf0ed1e1a7851a114d862e4df9b31d0802815772044`
- Family independent `AUDIT.md`: `b645448d86f3041df3c406f88640cd7f9c73aee11715b6b9eb43310a352a5799`
- Real-input `PROOF.md`: `58e75fba06c017fb8e2e59925b03a3b96e389e268ea257db79d1f5201b3a7b1d`
- Real-input independent `AUDIT.md`: `34d1c28ad1bfc4f21a96bb28aed20f23e52f5c636999f255cc61a40e75d6589f`
- Inert Pell source: `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`

Fresh independent algebra and presentation-data programs were written, fully displayed and inspected before execution. They import no author module and read frozen JSON only as data. No author constructor, author scientific checker, upstream program, physical simulator, collision selector, saved physical schedule or proof assistant was executed. This review does not independently reproduce the release-tool security audit or claim formal verification.

`INPUTS.before.sha256` and `PRESERVATION_CHECK.txt` record unchanged bytes for the six core proof/source/audit files. The independent programs write only into this new review directory.

## Corrections found and resolved

1. **Coordinate clarity in the real-input algorithm.** The persistent iterate is `q=g`, updated by the gap return `M`. The supplied physical guard rows are expressed in `(D,X,Y)`. The initial manuscript's instruction to test the chamber rows at `q` did not explicitly distinguish these coordinate systems. Final Section 7.3 now evaluates supplied rows at `Qq`; Section 7.1 explicitly defines the gap-coordinate chamber as their pullback through `Q`. This is the correct rational semidecision and agrees with `QM=NQ`.
2. **Acceptance-witness wording.** Section 10.2 now says that when `Delta>0`, a positive acceptance witness exists for each contact. It no longer uses wording that might suggest arbitrary positive witness values satisfy the fixed equation.
3. **Synthetic index-range wording.** Section 11.2 now places the zero-gap point `k=0` in the checked index range, avoiding the misleading antecedent “tail” immediately after the accepted tail `k>2`.

Only source lines 350, 379, 508 and 612 changed. Only physical PDF pages 11, 12, 16 and 20 changed. All four were directly reinspected after rebuilding; the other 18 pages are byte-identical to their directly inspected initial counterparts.

One cosmetic item remains nonblocking: reference [1] says “Example 1 and Sections 3.3” rather than singular “Section 3.3”. It neither changes the cited location nor impairs interpretation.

## Physical chronology and parameter scope

The Pythagorean parameter conditions cover precisely the rational infinite-order planar rotations. Primitivity excludes zero legs, forces odd `c`, and makes both legs coprime to `c`. A finite-order eigenvalue would make `2a/c` an integer, contradicting odd `c>1`. The converse denominator-one exceptions are correctly excluded. The choice of machine, alphabet and word occurs after the rotation and positive rational scale are fixed; only the live population is uniformly five.

The shear identity has the correct signs, including negative `a` and either orientation. Since `c+a>0`, both subdivision counts are finite and both step sizes have magnitude at most one quarter. The outer equal x-shear factors remove chronological matrix-order ambiguity. The reflected y block uses `D-y` and gives the claimed positive centered y-shear coefficient.

For `L`, the four principal times and all four spectator times follow from the messenger's straight legs. Endpoint inequalities keep the moving target between fixed neighbors, and its speed has magnitude below one. Thus there is no extra messenger recollision, target/spectator collision or remote simultaneous collision. Failed endpoints force an extra/tied contact or collapsed timing. For `H`, the target-nearest-to-anchor hypothesis is essential and is satisfied in every use; the spectator return ordering follows from `t'<q`. The translation's intermediate position lies between start and finish for both signs, so the reduced endpoint guard is exact, not merely sufficient.

Closed block endpoints give `4n+4` supplied rows per block and `4K0+12` overall. The first-failed-checkpoint argument establishes necessity as well as sufficiency for the complete collision word. The center remains strictly inside every guard regardless of total shear size. Initial order makes the normalized chamber bounded.

Contraction scales inner targets first; expansion scales outer targets first. These orders preserve all neighbor inequalities for arbitrarily small or large positive scale. They add 24 events and no guards. The finite messenger-label grammar has distinct-speed binary inputs and outputs, no conflicting prescribed input sets and a number-preserving identity completion. The population/type/speed distinction is maintained.

The rational duration row and the Zeno iff proof are correct. For contraction all positions lie within the shrinking macro interval and the duration has a geometric upper bound; the rational resolvent yields the clock. For scale at least one the two transfers alone make total time diverge. Nothing asserts continuation after accumulation.

## Geometry and the three finite-sign obstructions

For each centered guard, the squared line distance and perpendicular contact formulas are correct. Center positivity and boundedness ensure a positive attained radius and at least one rational nonzero contact. On the critical circle, only minimizing guards can vanish, and only at their contacts. Above the radius a nearest guard excludes an open arc, so density proves eventual failure. This establishes the exact disk plus punctured-circle formula for all fixed family members.

Duplicate rows, duplicate contacts, co-orbital contacts and initial-face contacts are handled correctly. On a contact's full orbit, the finite contact-index set has a maximum; rejected indices form the entire backward tail and accepted indices the remaining forward tail. Both rational tails are dense. At most three critical-circle points have zero initial gaps, so deleting inadmissible points does not destroy the rejected dense tail. The rational polynomial-sign obstruction is therefore genuinely about positive admissible gaps.

The integer obstruction properly uses eventual signs of homogeneous components. It does not assume the proposed integer-input formula was homogeneous. Correctness on every integer multiple, followed by clearing denominators, would imply the impossible rational classifier. Quantified integer witnesses are not covered by this finite-sign argument, as the manuscript explicitly states.

## Rational arithmetic and the literal certificate

The exact denominator proof works over `(Z/pZ)[i]` without treating that algebra as a field: modulo each odd prime dividing `c`, `z^n=(2a)^(n-1)z` has both coordinates nonzero for positive `n`. Thus neither coordinate cancels a factor of `c`; exponent zero is handled separately. This covers composite and prime-power denominators. Repeated division by the whole integer `c` determines the only possible exponent and does not assume a prime-adic valuation law or a coprime remaining factor.

The fixed-machine `O(L^3)` bound is conservative and justified: fixed-many rational operations retain `O(L)`-bit quantities; the forced exponent is `O(L)`; multiplication by a fixed Gaussian integer has polynomial cost. It is not a witness-search or compilation bound.

The contact quotient `(U+iV)/Q` has the correct sign and denominator. The Bezout equation gives joint primitive reduction even with zero/negative numerator coordinates. The canonical factorization, four bounded-coordinate slacks and enlarged radix extract the Gaussian coefficients uniquely. Negative `a` cannot invalidate the second positive-base POWER call. The inverse orientation requires `v+sign(b)S`, as printed. The shared natural radius witness and strict positive acceptance witness give exactly the intended interior/boundary predicate.

The fifteen POWER equations match the positive-index branch of the inert Pell characterization and the positive-base power theorem. The index shift `e+1`, strict modulus slack, positivity of the divisor/multiplier witnesses, and ordinary-versus-truncated subtraction are all justified. In particular equation P13 gives `alpha>w>=B0`, so `alpha-B0` is legitimate natural subtraction. Both soundness and existence survive the positive-domain adapters.

The ledger is correct: six natural leaves, six positive leaves and sixteen leaves for eight signed quantities, plus two 26-leaf modules, give 80 per contact and one shared radius leaf. Outputs are not double counted. There are 43 residuals per contact and one shared residual. The POWER residual degrees are `4,4,4,2,2,3,2,2,1,1,1,2,6,2,2`; P13 has leading term `-w^4 g^2`. Sum-of-squares leading terms cannot cancel, giving exact degree twelve. The optional Cantor transport adds four leaves and two quadratic equations. No finite-fold or arithmetic-DAG claim is implied.

## All-real topology and BSS scope

The family extension correctly uses an admissible nondegenerate closed arc rather than assuming the entire critical circle lies inside the positive-gap triangle. On that perfect compact arc, the excluded set remains countable and dense. The Baire argument proves that its complement is not relatively `F_sigma`; continuous pullback transfers the obstruction to actual positive real gaps. The open-guard representation supplies `G_delta` both relatively and ambiently.

For a fixed integer witness tuple, existential real projection of a finite polynomial-sign formula is semialgebraic. The countable union over integer tuples is therefore `F_sigma`, contradicting the proved class. The argument projects a semialgebraic set, not an arbitrary `F_sigma` set. It allows arbitrary fixed real coefficients and unbounded finite-dimensional real witnesses, without extending to arbitrary mixed quantifier alternation.

Finite BSS accepting paths have semialgebraic domains with all division restrictions retained. Their countable union is `F_sigma`, even with finitely many arbitrary real program constants. The corrected rational guard loop semidecides invalidity, including equality failure. Thus proper co-semidecidability in the stated finite-time field-operation model is established. The manuscript preserves the distinction from encoded rational decision, integer-input Diophantine certificates, Type-2 computation, oracles and physical limit instructions.

## Fresh independent supporting checks

`ALGEBRA_RECEIPT.json` records:

- All 45 fixtures: exact closed-form reconstruction of every supplied guard row/name, duration row, returned gap matrix, counts, squared radius, nearest rows and contacts
- 13,572 binary rules checked for two-to-two shape and distinct input/output speeds; 3,336 guard rows and 2,976 recorded phase ranges counted
- Generic symbolic shear/conjugacy and primitive-world-line identities, plus residual-degree checks
- 1,240 denominator/radix cases from 40 signed/coordinate-ordered triples with `c=5,13,65,169` and exponents 0–30

This fresh check does not claim complete reconstruction of every rule identity/phase field; that stronger separate audit is accurately attributed in the manuscript. The 12 negative controls, 101 synthetic indices and original 672-case tests remain the frozen independent audit's evidence, not newly rerun tests here. General enormous Pell witnesses are not instantiated.

`PRESENTATION_DATA_RECEIPT.json` verifies all 15 fixture-table rows against all three scales. It independently recovers the example polygon's seven feasible rational vertices, checks the plotted decimal coordinates within half of the last displayed decimal unit, and checks all fourteen displayed inverse-orbit points and the radius. The figure is faithful analytic geometry and is explicitly not a complete drawing of the dense excluded set.

## Prior work and visual review

Fresh primary-source checks confirm the manuscript's restrained attribution; details and links are in `SOURCE_CHECK.md`. Conservative arithmetic/shrinking, dense rational-rotation invariant obstructions and earlier linear-loop nonsemialgebraicity are recognized as prior art. The general BSS/topological and real-projection ingredients are attributed and independently explained. The contribution is limited to the explicit physical family and its exact classifier/certificate specialization; the bounded search is not converted into a novelty guarantee.

Every initial page was directly viewed at full-page resolution. The four changed final pages were directly viewed again. Independently running Poppler at 120 dpi from the final pinned PDF reproduced all 22 author render images byte-for-byte, and independent layout text extraction matched the final build text exactly. The title, contents, figure, table, displayed equations, page numbers, final hashes and references are readable. There is no clipped/overlapping text, missing glyph or overfull equation.

The final TeX log contains the expected disabled-shell-escape epstopdf warning and one benign underfull hbox at bibliography lines 685–688 (badness 2608). The latter is visible only as loose spacing in the commit/source entry and is not a release blocker. No overfull box, undefined reference or missing-character diagnostic was found.

The final verdict is **PASS with the explicit limitations above**, for the exact source/PDF bindings at the top of this review.
