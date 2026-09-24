# Factoring the packed mask: 93 arithmetic operations

The universal polynomial system, fixed admissible indices and positive
witnesses of `SHIFTED_AFFINE_94_PROOF.md` admit a certificate with
**93 operations: 50 multiplications and 43 additions**. There are still
34 positive unknowns, 22 equality tests and three fixed index parameters
besides the queried input. Fixed numerals and equality tests are free.

This is a shorter certificate for exactly the same system. No encoding,
source equation, admissibility bound or positive-domain condition changes.

## The five-instruction replacement

Write `Tcoef=1+theta*lambda`, as already computed. The packed mask is

    Tplus = q^2*Tcoef - ell*b + theta*ell*q^4.

Instructions 28--33 of the 94-operation schedule evaluate it by

    Tq4 = Tcoef*q2
    lbm1 = ell*b
    T2 = Tq4-lbm1
    packed_target_shift = ell*q4
    mask_term = theta*packed_target_shift
    Tplus = T2+mask_term

These are four multiplications and two additions/subtractions. Replace
them by

    Tq4 = Tcoef*q2
    theta_q4 = theta*q4
    mask_gap = theta_q4-b
    indicator_mask = ell*mask_gap
    Tplus = Tq4+indicator_mask.

Distributivity proves the unconditional integer identity

    q^2*Tcoef + ell*(theta*q^4-b)
      = q^2*Tcoef - ell*b + theta*ell*q^4.

The replacement uses three multiplications and two additions/subtractions,
saving exactly one multiplication. The four deleted temporary registers
have no consumers outside this block and are absent from every equality
test. The retained output `Tplus` (named `T` in the schedule) has the same
value for every integer assignment, even before any equation is assumed.

## Complete equivalence and positivity

Every other instruction and every equality test is unchanged. Consequently
the new schedule and the old schedule have exactly the same accepted
assignments of all inputs and supplied positive unknowns. The witness map
is the identity in both directions. The complete universality and decoding
theorem therefore follows directly from `SHIFTED_AFFINE_94_PROOF.md` and
its affine-radix predecessor, without another carry or Pell argument.

The new temporary registers do not introduce supplied unknowns or new
domain conditions. In fact they are positive on the existing domain:
`theta=H+b>b`, `q>=1`, and hence `theta*q^4-b>0`. As in all preceding
schedules, subtraction itself is certified by its reversed addition.

The full count is

    94 - 1 = 93 = 50 multiplications + 43 additions.

The literal numerals remain exactly `{1,3,8,15}`. The input and all fixed
index parameters retain their old meanings and values.

## Reproducible verification

`../verification/round34_1980_factored_mask_certificate.py` verifies the
precise six-to-five instruction replacement, absence of outside uses for
deleted temporaries, exact equality of every retained register, all 93
primitive arithmetic checks, all 22 source residuals and their unchanged
acyclic corrections. It checks that the set of source equations, positive
unknowns, parameters and free equality tests is identical to the
94-operation system and records the exact numeral set. Its JSON receipt
contains the complete instruction and residual lists.

This establishes an upper bound of 93 for the chosen measure. No lower
bound, optimality result or new Lean proof is claimed.
