# Retained sources and dependency boundary

All five Lean snapshots were copied byte for byte from the retained reading set at commit 5c9a442d263632fdcd4e9690154c12c2dcc70b53. Their size, SHA-256 and Git blob SHA-1 match that set. This is local retained-byte consistency, not a fresh remote retrieval, Git ancestry proof or claim about later revisions. No source theorem is invoked with a false primality hypothesis.

The public ZIP contains only these relevant Lean source snapshots, rather than complete earlier reports or a repository checkout. The common repository path is Combinatorics/Ramsey/Lean/GowersSzemeredi/.

## Definitions.lean

82-94: modular progression carrier and properness; 135-137: unnormalized Fourier transform; 227-229: ambient LinearOn; 277-279: centeredAbs; 311-330: Freiman and additive tuples.

- Retained URL: https://github.com/VladimirReshetnikov/ProveIt/blob/5c9a442d263632fdcd4e9690154c12c2dcc70b53/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean
- Bytes: 15504
- SHA-256: 17241a9ffa53e2c6b335eb326920952a7f3da25e5e5a601a7aca5606462f5e4b
- Git blob SHA-1: 97113b7afa6925a2dd4b76641eeaeff09597ab6a

## Proofs13BilinearExtraction.lean

16-32: prime-qualified budget theorem, exact cutoff, six budgets and existential output order F/G/H/J; 39-46: width propagation from the lower length target.

- Retained URL: https://github.com/VladimirReshetnikov/ProveIt/blob/5c9a442d263632fdcd4e9690154c12c2dcc70b53/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13BilinearExtraction.lean
- Bytes: 2863
- SHA-256: 9ce5b98fa823afda968e31ddbdfc76d684e34a3a566d4499d195cab6ccd4547f
- Git blob SHA-1: a17d646c96ddfd1dd05a5c203a15669945b8c0b3

## Proofs13CompleteRowExtraction.lean

14-42: prime-qualified affine partition input; 46-52: corrected lemma_13_7_holds. Included to document scope, not as a theorem used in the obstruction.

- Retained URL: https://github.com/VladimirReshetnikov/ProveIt/blob/5c9a442d263632fdcd4e9690154c12c2dcc70b53/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13CompleteRowExtraction.lean
- Bytes: 2426
- SHA-256: f0bcfc7913e27d811d8c001d396e828ccde24a11f8cb0c6831c8f6300e9664d5
- Git blob SHA-1: cd319ad022b37f0daeba2e506d3d02c64f4bbe9e

## Section10.lean

434-454: exact cutoff, spectrum bound, natural ceiling and corrected section10Zeta including its denominator.

- Retained URL: https://github.com/VladimirReshetnikov/ProveIt/blob/5c9a442d263632fdcd4e9690154c12c2dcc70b53/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section10.lean
- Bytes: 24924
- SHA-256: 8b63d784485ba8291b614a9153399cae216d2adaf37c9770344521083523cb2d
- Git blob SHA-1: 302e8a223f56dcdabf29f30ca3c80ac62a7adbfc

## Sections12_13.lean

60-99: arrangements and global/fixed-height counts; 198-247: vertical edges, fiber counts, differences, sections and Freiman predicates; 258-262: LinearOnDomain; 304-331: context, good heights and weights; 333-368: Stage 13.4 exact floor and full predicate; 385-406: strong/critical heights and Stage 13.5; 415-454: Stage 13.6; 465-500: weak/full Stage 13.7; 502-525: distinct all-moduli and prime-qualified target propositions.

- Retained URL: https://github.com/VladimirReshetnikov/ProveIt/blob/5c9a442d263632fdcd4e9690154c12c2dcc70b53/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections12_13.lean
- Bytes: 28878
- SHA-256: 6e6318bcce96a0e2023f6743d9c52cc1f9bd6b416beeeec6c3841916334743d8
- Git blob SHA-1: 1de556b791c7dac188d91f554231b11e2cf31cea

## Earlier reports

Report280, Composite modulus obstructions to Stage 13.7, 7 October 2026, frozen release v2. Section 7 provides the preceding full-budget dyadic construction; Section 8 provides the basic prime-power mechanism with fewer simultaneous input properties. Retained TeX SHA-256: 4c5c62d4a4e017be01a08d30aaa7f2408327d0828eae9cf84964260744f4dc64. That frozen report remains unchanged and is not included here.

Report281, Explicit uniform density square extraction with a sharper side length, 7 October 2026, frozen release v2. Lemma 3.1 provides the pure scalar margin 2 beta < u v, reproduced in full in this article. Retained TeX SHA-256: 81fb40560d306ab0e5927bd81742fefae5b25126bcb06ae166ade83fca65d2ff. No analytic extraction theorem, prime-modulus conclusion or newer source pin from that report is imported. Its full text is not included here.

## Mathematical additions in this report

Fix r >= 2 and s with r^s >= 8r. For every sufficiently large N with r^s dividing N and rad(N) dividing r, the canonical strip context simultaneously supplies selected genuine exact-cutoff Stage 13.4 and Stage 13.5 data, a displayed genuine Stage 13.6 record and all six literal budgets. One list of eight positive-power thresholds suffices. Every one of the r spectral aliases is covered and canceled by the selected step r. The exact ceiling in the Section 10 radius equals K, and its denominator is retained.

The uniform scalar inequalities beta < u(q) and beta < u(q)w(q), together with c < d/8, let the shared width budget force positive initial lengths through both the floor and predecessor branches. Thus every genuine alternative D/E has nonempty critical heights without requiring its own M or the other five numerical budgets. Under the radical-support hypothesis, the total floor map has at most r ambient affine agreements globally. The resulting row cap contradicts W delta = 2^92 a^-480 > r for every possible continuation.

A separate width-only argument forces every alternative normalized spectral radius below 1/4. At one critical height, the exact annihilator spectrum and the sharp 1/3 finite-subgroup rigidity threshold then show r divides every representative of step(Q). This excludes genuine initial packages with unit Q step, and Stage 13.6 continuations with unit R step, for this specific context and scale, and recovers the sharper one-point row cap. It makes no divisibility assertion about the Stage 13.4 P step. It does not assert a classification of unit-step contexts or all composite moduli. The original prime-power threshold is unchanged as a corollary.

The fixed-support construction needs r^s | N for strip integrality and r | N for no-wrap cancellation and kernel size. The sole use of rad(N) | r is invertibility of r*xi-1 in the global affine-agreement lemma. A small r=2, N=80 example demonstrates failure of that cap outside support and is explicitly not a full-budget witness.

The source pin and five snapshots are unchanged. The new proof is ordinary mathematics, not a source theorem invoked beyond its prime-qualified scope, a Lean build, a kernel certificate or a priority claim.
