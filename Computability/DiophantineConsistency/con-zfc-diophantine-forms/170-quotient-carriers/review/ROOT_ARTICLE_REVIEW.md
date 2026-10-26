# Independent mathematical review of the article

Reviewer: the separate compression-research agent. Date: 25 October 2026.
This is an ordinary mathematical peer review, not a proof-assistant
certificate. No article source was edited by this reviewer.

## Compact construction: `report/compact_proof.tex`

The four complete polynomial definitions match the accepted independent
sources: thirteen positive variables with 70 operations/degree206,
71/162, and72/154; twelve positive variables with 74/438.

Reviewed the order of unit extraction and coprime root recovery, the
early deduction `Nt=1 => C>0`, all pre-index bounds, normalized strong
rank, signed main-index recovery, the residue-sign exclusion, restoration
of a strictly positive quotient, and fresh cofinal completeness.
The smaller-modulus construction correctly requires `q^4 | S^2`; it
does not assume `q^4 | S`. Its full first-Pell recurrence restores
divisibility by `E` after identifying the exact first index.

The twelve-variable proof correctly applies prime valuations to a
rational carrier, uses the inherited adjacent-coefficient integrality
lemma, excludes the zero quotient, and obtains positive completeness
by a cofinal strong completion. Its argument does not assume a global
sign for a square root of one modulo a composite modulus.

The only suggested wording correction was to state the two coprimalities
explicitly as `gcd(A,F2)=1` and
`gcd(A*F2,(Q-1)*(Q*V^2-1))=1`, avoiding a possible reading that asserts
coprimality with `t^2`. That correction is present in the current article.
The independent literal-source checker separately verifies every live
gate, the exact local polynomial identities, all complete homogeneous
leaders, the fixed coefficient tuple, and the attained degrees.

Conclusion: mathematically accepted, relative to the explicitly retained
ordinary indexed-native/refutation calibration.

## Projection and pooled powers: `report/projection_proof.tex`

Compared the article against `agent_alternative/direct_pool/PROOF.md`,
its frozen diagonal-source proof, the inherited orientation-first
proof, and `agent_audit/new_construction/RADICAL_PROOF.md`.

The pooled identities were checked by expansion:

    S-2nH = T*L,
    sum_i(D_i-nY_i)^2 = S-2nH-T*sum_i Y_i^2.

The signed-index argument is valid because `T=-1 mod n` makes the
base invertible modulo `T`. Clearing negative indices by `n^b` gives
nonnegative polynomial-power errors. The bound

    0 <= Eerr <= 4*r*b^(4*b) < W^(2*b+1) <= W^W < |T|

holds for the stated `W>=258`, `r<=15`, and
`b=floor(sqrt(W-1))`. It forces every requested power exactly and
excludes negative indices at the two nonunit bases.

The strict local ranges are properly treated as a semantic existence
change with a larger cofinal horizon. The actual surviving power atoms,
principal Pell rows and complete orientation pool are retained before
power interpretation; the sign argument therefore remains acyclic.
The literal count is 234 coordinates/171 residuals after tightening,
then 223/160 after the two pooled blocks.

The common-Hessian-kernel projection proof is correct. Its hypotheses
give `Q_j(y+v*t)=Q_j(y)+a_j*t`; the unit slope supplies the integral
polynomial restoration `t=-a_s*Q_s(y)`. Projection and restoration are
inverse on the zero sets, with no divisibility assumption. Subsequent
integer elementary row operations preserve common vanishing and are
correctly distinguished from equality of the sum-of-squares polynomial.

Conclusion: mathematically accepted. The separately inspected selected
metrics are 217 unrestricted integer variables, 154 quadratic residuals,
19,112 collected quartic monomials, and coefficient height 5,184.

## Direct arithmetic: `report/direct_proof.tex`

Reviewed the full schedule from the orientation frame to arithmetic
interpretation. In particular:

- The affine class `q=6z+3` makes both pooled bases nonzero nonunits
  before their signs are inferred.
- The first individual power gives `F=t^t`; the recovered representative
  and exponent signs give `H>=3`, `y>=F`, `B!=0`, and then `x>=1`.
- The beta endpoints give `x>=2+(t+1)y`. The resulting bounds
  `|q|>=9|B|^2`, `|B|<=|q|/9`, and the bounds on denominator exponents
  require no positive-radix premise.
- The first binomial digit is interpreted using an open centered
  remainder interval, valid for either sign of the radix. Its explicit
  geometric bound forces `B=binom(F+t,t)>0`, followed by `q>0`.
- Both prime-power covering statements were checked by valuations:
  every row has a full prime power exceeding the horizon, and every
  prime factor of the binomial coefficient covers at least one row.
  Pairwise coprimality of consecutive factors is never assumed.
- The inherited local bounds are preserved by the larger majorant
  and the stronger endpoint estimate. The boundary `y=F` is excluded
  only after local extraction, by zero propagation in the accumulator.
- Completeness chooses the strict cofinal horizon first, then the
  diagonal value, beta spacing, code and CRT representatives. The
  parity statements are valid: `v2(F)>=t>v2(t!)`, the binomial
  coefficient is odd, and the final radix is 3 modulo 6.

Also read `report/diagonal_background.tex`. The bounded-list separation
lemma correctly needs an initial length bound on only one list, and
its strict coefficient-difference bound remains valid at coefficients
equal to `F`. The elementary `lcm(1,...,t)^2<=t^t` estimate and the
oddness proof are correct.

Conclusion: no mathematical correction needed, relative to the named
inherited arithmetic ledgers and C222/ZF/ZFC logical calibration.

## Optional conversion of the 12-positive source to 36 integer variables

Substitute independently for every positive coordinate

    x_j=1+a_j^2+b_j^2+c_j(c_j+1),
    a_j,b_j,c_j in Z.

This expression is always positive. Conversely, for any integer `N>=1`,
the number `4*(N-1)+1` is 1 modulo 4, hence is not excluded by the
three-square theorem. In a representation as three integer squares,
exactly one square is odd. Writing it as `(2c+1)^2` and the other two
as `(2a)^2,(2b)^2` gives the required representation of `N`.

The substitution is therefore surjective onto the positive integers.
It preserves zero existence, produces 36 unrestricted integer variables,
and adds seven binary operations per coordinate:158 operations in all.
The exact degree is 876. For a direct noncancellation witness, take the
previous degree 438 distinguished monomial and select only the `a_j^2`
summand in each substituted leading quadratic. Its exponent vector can
arise from no other original monomial, so its nonzero coefficient
survives unchanged. No generic-specialization assumption is required.

This optional lift is a consequence of a classical representation
theorem; no novelty is claimed for the positivity parametrization.
