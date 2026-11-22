# Independent mathematical review

This review checked selected high-risk steps. It is not a claim that every
line of the full report has been independently formalized.

## Measure chapter

The existing packet's displayed separate-tail pointwise inequality is false:
`x=2K`, `y=-K`, `K>0` makes its left side `3K` and its right side `2K`.
The common-dominator inequality in the current object-iPRA
`Probability.TruncationEstimate` is different and remains valid.

The corrected clipping inequality and its finite weighted-sum form are
kernel-checked in this package. The rate

    q(k) = k+2+ceilLog2(2 U(k+2)),   N(k)=R(q(k))

gives the pairwise L1 bound `3*2^(-k-2)` from the two tail budgets and the
rho-Cauchy budget. For monotone U and R, the actual diagonal samples

    b_k = S(N(k+2), k+2)

form a regular name. For `j>=k`, their underlying family indices both lie
beyond `N(k+2)`; the pairwise distance is bounded by `2^(-k-2)`, and the two
sampling errors give at most `2*2^(-k-2)+2^(-j-2)`.

The object/metatheory boundary is stated correctly: the programs U, R and S
are fixed primitive-recursive schemas, whereas k, n and finite lengths are
numerical inputs. Completion semantics is separate from the finite numerical
contracts. Two small corrections found during review were incorporated:
the scalar distance name samples both input names at `k+1`, and the halting
martingale example delays every simulated machine so its first possible
halting step is at least one. The chapter also spells out the countable-event
union precision allocation.

## Homological perturbation defect identity

Write `e=ip`, `L=1+delta*h`, `R=1+h*delta`, `E=R_N`, and
`B=delta-E=L*A_N=A_N*R`. From

    M_N=d*A_N+A_N*d+A_N*e*A_N

one obtains

    L*M_N*R = L*d*B + B*d*R + B*e*B.

The terms independent of E are

    L*d*delta + delta*d*R + delta*e*delta
      = d*delta+delta*d + delta*(h*d+d*h+e)*delta
      = d*delta+delta*d+delta^2
      = 0.

The remaining terms are exactly

    -L*d*E - E*d*R - delta*e*E - E*e*delta + E*e*E.

This independently confirms the signs in the report's inverse-free defect
identity. Multiplying by the two convergent inverse bounds is justified only
after the separately stated small-norm assumptions on both `delta*h` and
`h*delta` have been supplied. The exact rational matrix tests provide
additional implementation evidence, not a substitute for this general
algebraic argument.

## Formal verification scope

The standalone Lean replay checks 58 named host theorems, two proof-bearing
constructors and four exact rational examples. Every named theorem's axiom
list is recorded. The standard dependency union is `propext`,
`Classical.choice`, and `Quot.sound`; no admitted proof or new correctness
axiom is present. These are not newly compiled object-iPRA derivations. The
full completed-name Vitali assembly and homological perturbation formalization
remain explicitly identified proof obligations.
