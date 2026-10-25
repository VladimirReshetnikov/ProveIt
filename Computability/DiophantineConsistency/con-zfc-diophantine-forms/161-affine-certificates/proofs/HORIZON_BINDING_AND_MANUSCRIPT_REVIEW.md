# Supplement: literal horizon binding and final manuscript review

Reviewer: pell_route, a separate AI-assisted research agent in this task.
Date: 25 October 2026.

This supplements `INDEPENDENT_AFFINE_AND_HORIZON_REVIEW.md`. The earlier
document proves the semantic admissibility of the signed affine changes
and the proposed horizon change at the inherited interfaces. The present
review binds those changes to the actual emitted source and examines the
main manuscript, including its new horizon section.

## Verdict

The emitted raw horizon source has exactly the intended four semantic
mutations. Its power requests, square frame, and signed index bindings
remain literal identities for the intended actual values. The horizon
root is private and is deleted correctly. No additional raw-row or
metadata change was found.

I found no unresolved mathematical error in the main manuscript's new
arguments, including the signed-radix authentication and the allowance
of horizons starting at one. This is a review of ordinary mathematics
composed with explicitly retained interfaces. It is not a claim of a
new end-to-end proof-assistant verification or a reconstruction of the
entire transitive logical-calibration dependency closure.

## Independently checked source identities

The standalone checker `audit_horizon_binding.py` was written for this
review. It imports only Python standard-library modules, not the builder,
its algebra engine, or the predecessor's checker. All arithmetic is exact
integer sparse-polynomial arithmetic. Its explicit semantic request
table is fixed independently of the producer certificates.

The parent archive has SHA-256
`38dfec4f7db8ba4af921fe101714da6a569a3afce1d916325eb550160372c913`.
The new raw source has SHA-256
`3a31760c82dc14223058e3c79ca1ca3efc26de543824cd24ea018204af559bf5`.

All raw coordinates, metadata, and residual labels are identical to the
parent. Exactly these residual polynomials change (indices are zero-based):

| Row | Retained label | New polynomial |
| --- | --- | --- |
| 363 | `cofinal.horizon` | zero |
| 381 | `growth.base_definition` | `d - 2^27 t0 - 33*2^26` |
| 382 | `radix.odd_square` | `q - 4z - 1` |
| 383 | `beta.odd_square_multiplier` | `s - 2v - 1` |

Here the actual index is `t=t0+16`, so row 381 is exactly
`d=2^26(2t+1)`. The historical labels ending in `odd_square` are labels
only; their checked new polynomials are affine.

The actual first request is `(base,index,output)=(d,t0+16,F)`.
The same variable `d`, at raw coordinate 556, occurs in the square
frame and base-zero modulus `2Ad-d^2-1`. It is correct that the frame
row is unchanged: it already squares this dedicated base coordinate,
whose defining row now fixes the new large value. The checker verifies
all 37 distinct actual frame atoms, all 18 power requests, all five
base moduli, all 14 principal Pell norms and their pooled indicated
indices, and the derived consecutive-index request.

The raw horizon root is coordinate 523. It occurred only in row 363
in the predecessor; it occurs in no new raw residual. The unchanged
beta product row still fixes `y=F*s`, and the unchanged self-radix
base still fixes `BH=B*(2+sum of nine actual representatives)`.

Normal and optimized (`python -O`) executions passed. The retained
reports are `HORIZON_LITERAL_BINDING_AUDIT.json` and
`HORIZON_LITERAL_BINDING_AUDIT_OPTIMIZED.json`. The checker uses explicit
failure conditions, so optimized Python does not disable its checks.

## Terminal deletion and binding to the discriminant contraction

For both profiles, I independently replayed the two final monic affine
substitutions from the emitted transformed source. I verified their
restoration polynomials, the exact retained row and coordinate lists,
the complete renumbered residual lists, and the zero horizon row.
I also checked that the removed horizon coordinate occurs in no other
residual at this stage. Its omission therefore changes no existential
zero-set condition: a deleted unused integer coordinate can be restored
arbitrarily.

For the principal profile the deleted root and row are 215 and 158.
For the companion they are 214 and 157. The resulting inputs to the
additional discriminant contraction have 239/175 and 238/174
coordinates/residuals respectively. Their exact JSON objects are
identical to the actual `source_equation.json` files consumed by that
contraction, with hashes:

- Principal: `fcd3ec8cffb76f319eb90384f19ecca3ecbe791dce61ecc46ad3f6d8fd0f9b2b`.
- Companion: `c5ba04893db0d9b528dda8aa236ab1cf416344e999077adf455a6c8886b0b57e`.

The intermediate factorization, regenerated monic-projection lineage,
translations and coordinate shears, the discriminant contraction itself,
and the final quartic recollection are covered by the separate algebraic
review. The present checker does not import that review or pretend to
replace it. The two reviews meet at exact source objects.

## Mathematical points reviewed in the manuscript

I read the complete main `report/manuscript.tex`, including the signed
bootstrap, centered digit, factorial-free CRT, Horn multiset, completeness,
algebraic contraction, logical scope, and newly added horizon section.
The following matters are essential to the approval.

1. **The new horizon is recovered before the signed-radix bootstrap.**
   For every integer t the new base has absolute value at least `2^26`.
   Its frame square supplies the original orientation proof's size
   prerequisite without an assumed sign of t. Signed power recovery
   gives t nonnegative. At t zero the two beta endpoints contradict
   parity, even if y is negative or equals minus one. Thus t is at
   least one, and the later large-growth inequalities are legitimate.

2. **Negative radices are not silently discarded.** The affine class
   excludes minus two, minus one, and zero. The unit case one is ruled
   out using the last beta endpoint. For other radices the numerator
   requests force actual representatives nonnegative. The normalized
   remainder is integral with a centered absolute-value bound even
   for a negative denominator. Its comparison with the signed low
   binomial polynomial authenticates positive B before q is proved
   positive. The manuscript uses this logically sound order.

3. **The horizon-one case is retained throughout the estimates.**
   At t one, B equals `F^2+1`, and C may be zero. A positive C is
   unnecessary because H is at least two and binomial upper arguments
   may be zero. Every denominator exponent is positive and at most x.
   The coefficient estimates, prime-power row selectors, and Horn
   coefficient uniqueness only require t at least one and the stated
   large F, both of which are proved.

4. **The modified local bound is the right one.** The main low-height
   proof may use `Rmaj<2x` because it retains t at least 16. The horizon
   extension explicitly uses `Rmaj<3x` before the later exclusion of
   y equal to F. The dyadic estimate beginning at x equal to `2^28`
   proves `(3x)^(2^23)<2^x` with strict inequalities. The label-index
   bound also survives because F is greater than `2^22`.

5. **Completeness uses fresh witnesses for the changed growth law.**
   It does not claim that every new source zero restores the deleted
   square constraints. Large horizons remain freely available,
   `v2(F)=26t` supplies the required even multiple of t factorial,
   and odd CRT periods permit the parity choices needed for even x.
   Choosing even x makes q an odd square, which satisfies the weaker
   congruence `q=4z+1`. The former square multiplier is unnecessary.

6. **The algebraic contraction has the correct degree argument.**
   Substitution for D can create a cubic term, but subtracting the
   retained gate row times a removes it. D also occurs linearly in
   `shared.last_norm`; this occurrence remains quadratic after
   substitution. The current manuscript records that occurrence,
   so the proof no longer relies on the stronger false claim that
   D has no other live occurrence.

7. **The logical scope is explicit.** I additionally read the retained
   immediate declarations of `KEndpoint.c222_iff_zf_refutation` and
   `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Their
   immediate statements are unconditional and proof-bearing; the
   first requires no Turing-machine execution hypothesis. This does
   not by itself audit all imported Lean dependencies, a limitation
   the manuscript states. No unsupported global minimality or global
   novelty claim is required for the new reductions.

One notation collision was found and reported: Q denoted both a
normalized quotient and the absolute radix. The current manuscript
uses `Q_D` for the former and Q for the latter, resolving it.

## Reproduction and remaining scope

In this workspace the standalone finite check is reproduced by:

```sh
python sources/pell_agent/audit_horizon_binding.py
python -O sources/pell_agent/audit_horizon_binding.py --output sources/pell_agent/HORIZON_LITERAL_BINDING_AUDIT_OPTIMIZED.json
```

For incorporation elsewhere, the checker accepts explicit `--archive`,
`--source-root`, `--principal-d-input`, `--companion-d-input`, and
`--output` paths. Its pinned parent hash and fixed semantic request table
remain enforced.

This review approves the changes within the stated ordinary-proof and
finite-algebra scope. It does not promote the result to a global
smallest equation, independent discovery priority, or a completed
object-language ZFC derivation.
