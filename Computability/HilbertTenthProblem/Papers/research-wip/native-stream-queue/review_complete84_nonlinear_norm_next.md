# Independent review: nonlinear two-norm allocation and Cayley obstruction

**PASS within the declared scope.** No mathematical correction is requested. The polynomial classification, the obstruction to simultaneous integer chart coordinates at every parent positive zero, and the two paid evaluator counts are sound. None establishes a minimum for the complete source or improves its 84-operation bound.

## Frozen sources and coverage

The reviewed author note is `/tmp/complete84_nonlinear_norm_next.md`, SHA-256 `270a6ed4bc26fa598763fe518950d48cfa923240ecb7323e4e41d9b8f9c8e6ca`. I read its entire proof, including all qualifications and cost accounting.

The following dependencies under `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/` were authenticated:

| File | SHA-256 | Review coverage |
|---|---|---|
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` | Full note; inherited positive-zero and factor-unit interface |
| `complete84_affine_norm_pair_rigidity.md` | `eb67b76ac6a5c3150c37cf17c7e062fe6d19eae374adc8c27e8884fdebd58641` | Full note; actual rational coordinates and nonsquare coefficient field |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` | Supplied-port/factor metadata; literal rows 1–47 and 69–84; full-array structural comparison below |

The new evidence JSON `/tmp/complete84_nonlinear_norm_next_checks.json` has SHA-256 `39d2e0ad0ee227acac368680b9f90667475aa03952d9c6ac93ddf0432963cb2c`. Its helper `/tmp/complete84_nonlinear_norm_next_checks.py` has SHA-256 `bb46e086ac686cb8862499bd0ad3702c9b190161e2710d78bfb8f4738ac4d889`; this helper was authenticated only, not executed, imported, or independently reviewed line by line. No predecessor program or saved arithmetic array was executed. Fresh reviewer code performed data-only equality, graph, and count checks. The other historical scouts listed by the author were not rereviewed for this note.

## Polynomial classification

The actual rational coordinate substitution is invertible at the function-field level: the displayed formulas recover `eta, delta, rho, sigma`, and the exterior formulas recover the original `Jrep, w, s, x, zeta, alpha`. The fixed valid compiler numerals used as denominators are nonzero. This establishes a rational independence argument, not a free operation or an integer-domain substitution.

In the resulting coefficient field, `Delta=((X+1)Y+1)((X+1)Y+3)` has two distinct linear factors in the independent variable `Y`, each of odd valuation. It is therefore nonsquare. This argument is on the generic source coordinates; it does not impose a norm equation and then incorrectly reuse the resulting field as an independent cut.

Over `L=K(sqrt(Delta))`, the four old linear factors are pairwise nonassociate primes. The four output plus/minus forms are nonzero and multiply to their squarefree product. Each is therefore a scalar times a subset of these primes. Conjugation exchanges the members of each old pair. A subset cannot contain a whole conjugate pair, since its own conjugate would then repeat those factors in the full product. The two plus-subset cardinalities consequently sum to two and give precisely `(1,1)`, `(2,0)`, and `(0,2)`.

For `(1,1)`, disjointness forces separate old norm pairs. For `(2,0)`, the nonconstant plus form contains one member of each old pair and the companion is constant; the reversed case is identical. The scalar product condition is exactly `Norm(alpha) Norm(beta)=1`. Conjugating reconstructs coefficients in `K`, proving the converse. This also excludes translations and lower-degree corrections without a degree restriction. A collapsed output has transcendence degree at most two, so cannot be a birational replacement of four independent coordinates.

The classification is not a lower bound for circuits evaluating the quartic product, and does not apply to rational coefficients depending on the four replaced coordinates, a changed coefficient `Delta`, or equality restricted to positive zeros.

## Rational chart and integer obstruction

The identities `p^2-Delta*b0^2=d0^2` and `Dnum^2-Delta*cnum^2=d0^2*Nm` follow by expansion. Changing the sign of `b0` in the inverse matrix gives the claimed rational inverse while fixing `mu,kappa`. On the actual positive supplied domain, `v=kappa=u+delta*Delta>Delta>=8`, so `d0>0`, and both new coordinates are positive rationals before any equation is imposed.

At a parent positive zero, use the inherited **main-unit equation** `Nm=1`. It is justified by the accepted parent theorem; it is not inferred merely from an integer product equaling `Delta`. Directly, without a Pell-index argument,

    D*c' - c*D' = b0*(D^2-Delta*c^2)/d0 = 2v/d0.

If both new coordinates were integers, the left side would be an integer. But `Delta<=v-1`, `v>=9`, and hence `d0>=v^2-v+1>2v`, make the right side strictly between zero and one. This rules out simultaneous integrality at every parent positive zero. It does not say that neither coordinate individually can be integral, nor exclude another rational chart or a larger numerator/denominator encoding.

## Complete evaluator identity and paid boundary

The denominator-cleared evaluator leaves the other six factors on the original coordinates. It is not a substitution of `c'` into every auxiliary consumer of `c`. Its identity is exactly

    Fnum = Pother*(Dnum^2-Delta*cnum^2)-Delta*d0^2
         = d0^2*F84.

Thus it preserves the complete positive zero set on the valid compiler slice because `d0>0` there. The identity holds over every commutative ring; unrestricted zero-set equivalence fails to follow when `d0=0`.

The numerator schedule uses `5M+5A`, its norm `3M+1A`, and the final scale/target `2M`. Removing only the old `D^2` and main subtraction gives `98=56M+42A`. The old `c^2` and `Delta*c^2` producers remain charged because the auxiliary block still consumes them. Independently parsed receipt arrays have no duplicate definitions or forward references; all 98 rows and all 25 supplied ports are live. Exactly 81 parent rows are literal.

The alternative evaluates the original 84 computations and then appends one subtraction and two multiplications: `87=49M+38A`. The receipt has 83 literal old rows and the identical old final subtraction with its destination renamed `cayley_old_output`; this is a name change only. All 87 rows and all 25 supplied ports are live. Its output is the same multiplier polynomial. The data-only checks also reproduce exact equality between the receipt's embedded parent packet and the authenticated original JSON.

These are upper bounds for two specified implementations. Neither divides for free, eliminates a witness, improves 84, or proves any global optimum. No new degree, native-computation, or universal-language claim was certified in this review.
