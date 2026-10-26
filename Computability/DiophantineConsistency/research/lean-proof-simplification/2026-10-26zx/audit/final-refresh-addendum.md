# Final non-repetition refresh

Initial source/comparison pin: `9d9d1123b39927d30363f1dcd53c23f0575c30ee`.

Final comparison pin: `60fcb2a69b7f1fdd4c3592ea5f164223cad50abe` (commit timestamp 26 October 2026, 19:14:42 UTC).

## Effective coverage

The final tree contains 43 placed packets, `2026-10-26a` through `2026-10-26zq`. `docs/incoming` contains only its README. The five initial incoming ZIPs have become packets zk through zo. All 328 retained nonadministrative files in those five placements are byte-identical to members of their original archives: Git blob hashes were compared directly with the hash of each uncompressed ZIP member. Each placement additionally has its placement/omission administration. No unmatched retained payload occurred. The initial audit continues to cover the omitted original ZIP members.

| Final placement | Initially audited archive | Retained payload files matched |
|---|---|---:|
| zk | diophantine-lean-new-obligations-2026-10-26.zip | 34 |
| zl | Lean_Proof_Simplification_Power_And_Masks_2026-10-26.zip | 90 |
| zm | ProveIt_Lean_Simplification_Round5_2026-10-26.zip | 109 |
| zn | proveit-lean-additional-certificates-2026-10-26.zip | 53 |
| zo | lean-proof-simplifications-2026-10-26.zip | 42 |

The two genuinely new packets, zp and zq, were read from the exact final Git commit without changing the checkout. Thirty-seven report, note, patch, prototype, and review text files totaling 261,168 bytes were materialized. Main report bodies, further questions, supporting notes, late-review addenda, and candidate-specific code matches were inspected. The files and SHA-256 identities are recorded in `late/late_text_manifest.json`. This is a bounded novelty review, not a fresh compiler audit of the new packets.

## Newly excluded mechanisms

Paths below are relative to the indicated `research/lean-proof-simplification/2026-10-26...` packet.

### zp: controller and reflected-word refinements

- `report.tex:137-215`, `evidence/reflection-review.md`: strengthen reflected-source normalization to every natural target offset, dropping `h <= 1004` and weakening the coefficient-position bound to `p <= 1005`. Lift through the finite reflected sum; optionally retain old wrappers. This does not generalize coefficient budgets or imply absence of carries.
- `report.tex:217-292`, `evidence/controller-notes.txt`: fixed prime support/unit certificate for Gamma at all `d*p^n`, preserving both independent exponents, natural-subtraction guards, and the one-way zero-exponent case. This substantially overlaps the already-audited incoming unit-certificate proposals.
- `report.tex:294-354`: translate any finite seed, using sum(S+t)=sum(S)+card(S)*t, to obtain prescribed-sum existence without triangular-sum evaluation. Coprimality/surjectivity of multiplication by the cardinality remains. Translation does not automatically preserve physical safety.
- `report.tex:356-418`: all-exponent LTE divisibility predicate as primary interface, recovering exact order uniformly. This overlaps the already-audited LTE spectrum proposal.
- `report.tex:457-481`: further directions include classifying genuine reflection bounds, packaging the fixed unit certificate, translation-invariant seed constraints, and general first valuation v_p(g-1)=s. These are excluded too.

The packet explicitly says its translation theorem neither re-proves nor removes CurrentDummySafety's physical nonwrapping premises (`report.tex:349-354`).

### zq: cyclic subset sums and controller interfaces

- `report.tex:215-320`, `lean/RestrictedSubsetSums.lean`: every proper positive cardinality `0<a<T` realizes every sum in ZMod T, with no coprimality. The explicit staircase/one-gap subset realizes every natural sum in the available window before reduction modulo T.
- `report.tex:322-446`, `lean/AffineSubsetCoverage.lean`: Boolean-free affine subset coverage by allowing cardinality `a <= C0` rather than `a < C0`, provided `0<C0<T`. Removes the auxiliary Boolean arithmetic correction and its coprime-cardinality selection. The actual parameter threshold and physical arbitrary-subset safety interfaces remain explicit.
- `report.tex:448-502`: fixed-factor consumers use annihilating periods instead of exact multiplicative orders; the auxiliary prime-power coordinate orbit still needs exactness.
- `report.tex:504-619`: one complete Gamma residue and coprimality transfer, overlapping already-audited fixed-modulus proposals.
- `report.tex:621-659`: arbitrary-exponent LTE annihilator law, also overlapping earlier incoming material.
- `report.tex:661-688`, `lean/LiftSeed.lean`: use the nonzero first-lift residue `g % p^2 = 1+p*c`, `1<p`, `c>0`, to derive `g>1`, `p | g-1`, and `not p^2 | g-1`; no separate `c<p` premise is needed. Keep primality/oddness for the order theorem.
- `report.tex:690-708`: specified-seed translation companion, overlapping zp.
- `evidence/late_head_scope_addendum.md`: optional removal of Boolean support branches, and finite composition of existing safe single-dummy increments into the selected subset, are explicitly advertised. This does not propose replacing the single-dummy safety proof by terminal-carry conservation.

## Four current candidate decisions after the refresh

| Candidate | Final novelty disposition | Closest prior and the surviving difference |
|---|---|---|
| Consume `DirectEnumerator.program` to prove `haltingTest_natPrimrec`, deleting the separately maintained extensional Primrec certification layer | Retain | Packet i's fun_prop proposal still builds the second extensional proof; packet e shares actual program builders. No deletion of the second certification route or this dependency inversion was found, including zp/zq supporting notes. |
| Prove the ordinary normalized dummy increment from terminal-carry zero on old and new words plus the exact nonwrapping support of the perturbation; remove the coarse quantitative safety chain | Retain subject to its stated mathematical/Lean validation scope | Generic telescoping and reset/finite-scan APIs are already assumed. Packets zn, zp, and zq explicitly retain/reuse existing physical nonwrapping bounds. The new residual obligation is their replacement by an exact boundary-conservation argument, retaining actual Boolean and placement hypotheses. |
| Replace `FreeCarrierRatio.shifted_Q_bounds` with the joint shifted-numerator envelope and denominator domination | Retain as a narrow local result | No exact Qstar/shifted_Q_bounds/envelope proposal found, including supporting .txt notes and zp/zq. Existing coefficient-majorant abstractions and broad earlier negative search mentions are not counted as new. Complete helper costs and actual checked replacement scope must remain visible. |
| Classically prove `ComputablePred`/`REPred` for the fixed constant predicate `fun _ : Nat => P`, shortening the non-effective `refutationInputs_re` endpoint while retaining the explicit enumerator | Retain only as an explicitly optional non-effective observation | No corresponding constant-predicate/fixed-proposition/non-effective-RE shortcut was found in report prose, supplementary notes, patches or new packet bodies. This does not compute a refutation program or decide consistency. Correct the old docstring claiming this particular proof proceeds via the actual verified enumerator. |

The constant-predicate option is logically available for every fixed proposition P. It must not be described as a new effective Diophantine construction, a uniform computability theorem in P, or a substitute for `DirectEnumerator.program`. Any proof-irrelevance statement about an existing choice-defined polynomial is a compatibility observation, not a way to extract a concrete polynomial from excluded middle.

The internal-division direction remains excluded: incoming zn's supporting `audit/exclusion_taxonomy.txt` already raises generic ordered-semiring division uniqueness. The later successful kernel test does not restore novelty.

## Source stability

Only five maintained Lean files differ between the initial and final pins:

- `ExecutableJones.lean`
- `JonesSyntax.lean`
- `NativeQuadraticPositions.lean`
- `ObjectPolynomial.lean`
- `SyntaxCoefficients.lean`

The Git blob identities of all eight checked candidate/source-boundary files are unchanged: `Computability`, `DirectScalarEnumerator`, `ScalarPRCode`, `CurrentDummySafety2011`, `CurrentDummyMutation2011`, `CurrentWordTopBounds2011`, `FreeCarrierRatio`, and `Polynomial`.

`late/final_refresh_identity.json` records the exact old/final identities, the five-archive relocation matches and changed-file list. This establishes source stability for the listed targets; it does not claim a fresh full dependency-closure rebuild at the final pin.
