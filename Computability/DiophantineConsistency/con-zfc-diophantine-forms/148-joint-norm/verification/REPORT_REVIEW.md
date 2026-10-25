# Internal mathematical and report review

The package was prepared with several collaborating AI agents. These reviews
were conducted separately within the same research session. They are not
external human peer review and do not replace a formal proof-assistant build.

## Principal construction

The arithmetic reviewer checked the signed-base power argument, the odd
multiplier, the magnitude bootstrap before signs are available, exclusion of
the zero-exponent branch, the denominator-ratio bound, signed low-tail
recovery, the separate zero-factorial branch, the rounded-factorial theorem,
and the constructive converse. The reviewer also checked the report against
the literal 245-variable artifact and the retained calibration interface files.

Two corrections and two scope clarifications were incorporated:

1. The product-bound identity has numerator `L*(t+1)`, not `L*(t+2)`.
2. The ordinary coefficient bound for a nonzero factorial candidate does not
   extend to the zero candidate. The latter now has its own `2^t` bound.
3. The semantic multiplier change preserves existence of zeros through finite
   refutations; it is not claimed to be a pointwise coordinate bijection.
4. The 202 constrained monic eliminations have polynomial restorations, while
   the 112 unused coordinates may be restored to zero. Discarding unused
   coordinates is not a bijection of all raw assignments.

The report now states the signed-base coprimality and numerical bounds
explicitly. Its rounded-factorial theorem covers all `t >= 4`; the source
retains `t >= 16` for the stronger common-norm margin.

## Compact companion

A separate reviewer checked the square-recovery order and the undoubled
strong-Pell-pair converse, and independently derived the complete leading
homogeneous part of degree 454. The detailed review is retained in
`COMPACT_INTERNAL_REVIEW.md` and `compact/INDEPENDENT_REVIEW.md`.

## Evidence boundary

No further substantive mathematical defect was identified in these internal
reviews. The finite replay receipts verify the specified polynomial objects
and finite transformations. The unbounded mathematical proofs and inherited
C222/native/refutation calibrations remain separately identified in the report
and component proofs. No fresh transitive Lean/Rocq build is claimed.
