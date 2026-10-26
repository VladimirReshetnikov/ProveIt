# Final bounded review against packets zc and zd

**Decision: retain both power patches under their exact narrow formulations.**
The final comparison cutoff is
`91dce223cda86c0755b8a9b2504f84be04443fce`. The measured source pin remains
`9f35798db4a63c25e435fca14d75931144657d7e`; no candidate or count changes.

The complete main reports for zc and zd were read, including their optional
directions and further questions. Relevant integration patches, prototype
proofs, and substantive review notes were also read. Exact paths, sizes and
SHA-256 identities for 18 read sources are in
`evidence/late_reviewed_sources.json`. Reads used local Git objects, not a
checkout update or remote fetch. No bundled script or Lean source was executed.
This is not a claim to re-read every unchanged whole-file source snapshot.

## zc: coefficient composition, scalar thresholds, computed quotient indices

Under `2026-10-26zc/`:

- `report.tex` section “Compose the coefficient bound instead of expanding a
  square”, and `patches/01-coefficient-action.patch`, move an existing linear
  encoded-polynomial multiplier bound earlier, apply it twice, and keep the
  old public alias. The future questions extend it to mixed products and
  arbitrary powers, with all interfaces and helpers counted.
- Section “Remove two scalar exponential inductions”,
  `patches/02-power-thresholds.patch` and `checks/PowerThreshold.lean` normalize
  the two exact natural-number threshold inequalities, using a single
  exponential variable or a shifted exponent. This does not concern modular
  multiplicative order, a guarded cast/divisibility iff, or CRT transport.
- The optional quotient section and its patch/prototype use the existing
  recovered tile index as actual computational data, prove equality to the
  legacy choice-based word, and discuss concrete computational consumers.
  This is now excluded even though it adds source. Our coordinate witnesses
  are unchanged; no computable representative or choice elimination is claimed.

After all three mechanisms and their future directions are assumed available,
the two power patches still remove exactly the listed fresh client proofs.

## zd: finite exact-order certificates are now explicitly old

Under `2026-10-26zd/`, `report.tex` section “Replace prime-divisor case trees
with finite order certificates”, `patches/02-prime-factor-order.patch`,
`evidence/reviews/arithmetic_findings.md`, and the independent review provide
a private monoid adapter from the finite set `n.primeFactors` to the existing
`orderOf_eq_of_pow_and_pow_div_prime` criterion. They replace
`CurrentControllerData2011.two_order_47` and `two_order_2011` by complete closed
finite certificates. The strict positive-candidate-order guard is essential.
`lean/checked/FiniteOrderCore.lean` independently checks first positive returns,
and the further questions explicitly consider more controller constants.

This corrects an earlier search-level observation that no previous `orderOf`
proposal had been found: it is **not** true at the final cutoff. The general
finite-factor certificate, both exact clients, and its further-client direction
are all assumed applied and receive no credit here.

The residual distinctions are concrete:

| Retained target | What remains after zd's certificate is available |
|---|---|
| `order_product` | Transport an already-defined power through the CRT multiplicative equivalence, then use product order; no candidate-order factorization or finite certificate is introduced. The redundant explicit mapped-pair witness remains removable. |
| `generator_cast_auxiliary` | Specialize the existing **parameterized** prime-power order theorem at zero and apply order-one iff; do not reconstruct any finite order certificate for a new constant. |
| `generator_cast_C0` | Specialize the existing full CRT order theorem at zero; the duplicate CRT proof remains even if both upstream finite certificates are already simplified. |
| `block_order` / private `order_transport` | Rewrite the modulus by the already-proved factorization. The private equality-transport wrapper is unrelated to how either factor's order is certified. |
| `pow_cast_eq_one_iff` | Fuse two directions of the same guarded characteristic-zero/divisibility rewrite. This statement does not assert an exact order, and every original cast API and lower-bound guard remains. |

zd also contains selector-cutoff logical duality, bounded natural-complement
cancellation with both guards, and a conditional numeric-control overwrite
facade for Boolean/support/capacity invariants. Its full prototype preserves
unconditional support and counts the proposed facade. These are all treated
as excluded; neither retained power patch changes tile colors, cutoffs,
digit support, capacities, controlled word definitions, or those interfaces.

## Comparison with the other retained round-five directions

The actual retained `units/patches/gamma_pos_from_coprime.patch` and
`masks/patches/bit3_clear_of_residue.patch` were read as well. They also do not
implement any zc/zd mechanism: zc's coefficient-composition and threshold
interfaces do not replace the `Gamma_pos` factor-by-factor positivity proof by
nonzeroness from the already-proved `coprime_Gamma_47`, or supply the exact
bit-3 residue rewrite. Likewise zd's finite-order,
cutoff, complement and controlled-update APIs do not discharge those residual
proofs. Their owning reviewers remain responsible for their other baseline
comparisons and late ze/zf review.

## Result and scope

No duplicate power candidate was found in these two fresh packets. This is a
bounded semantic comparison, not a mathematical-priority or compilation claim.
The two existing candidate files, two patches and total reduction of 21
physical / 20 nonblank lines remain unchanged; all proposed Lean is uncompiled.
