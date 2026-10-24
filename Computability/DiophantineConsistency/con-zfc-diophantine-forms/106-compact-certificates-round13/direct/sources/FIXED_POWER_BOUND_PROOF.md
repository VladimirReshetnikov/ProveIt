# Fixing the positive-power certificate bound

This is ordinary arithmetic research. Lean formalization remains paused.
No existing Lean source or frozen candidate is changed.

The positive Pell certificate for `m=n^k` has a free common bound `W`
and two nonnegative slacks witnessing `n<=W` and `k<=W`. For positive
`n,k`, all three coordinates can be removed by defining `W=n+k`.
Completeness requires constructing fresh Pell witnesses at this bound;
it does not follow by shifting a previously chosen `W`.

## 1. Completeness at every common bound

Write `(chi_a(j),psi_a(j))` for the nonnegative solution obtained from

```
(a+sqrt(a^2-1))^j=chi_a(j)+psi_a(j)*sqrt(a^2-1),  a>=2.
```

Fix arbitrary positive integers `n,k` and **any** integer `W>=n,k`.
In particular `W>=1`. Define

```
A=chi_(W+1)(W),  W*Z=psi_(W+1)(W),
T=2*A*n-n^2-1,  X=chi_A(k),  Y=psi_A(k),  m=n^k.
```

These are natural numbers. Indeed, the standard Pell congruence
`psi_a(j)=j mod(a-1)` proves `W|psi_(W+1)(W)`. Also `A>1` and

```
n^k <= n^W < (W+1)^W <= A.
```

The strict middle inequality uses `W>0` and `n<W+1`; the first uses
`n>=1` and `k<=W`. The elementary power lemma then gives

```
0<m<T=2*A*n-n^2-1.
```

For clarity, the elementary step can be checked directly: `n^k<A`
implies `n<A`, so `(A-n)^2<=(A-1)^2`; hence
`T=A^2-(A-n)^2-1 >= 2A-2 >= A > n^k`, since `A>=2`.
The Pell power congruence gives

```
X = Y*(A-n)+n^k mod T.
```

It follows either from the recurrence for `chi,psi`, or by reducing
`sqrt(A^2-1)` to `A-n` modulo `T`:
`(A-n)^2=(A^2-1) mod T`, so evaluation of the conjugate two-term Pell expansion
gives `chi_A(k)-psi_A(k)(A-n)=n^k mod T`.
The final Pell equation is exact:

```
A^2-((W+1)^2-1)*(W*Z)^2=1.
```

The finite indexed-Pell criterion used by the parent supplies its five
auxiliary Pell coordinates and associated quotient/slack coordinates
for `X=chi_A(k),Y=psi_A(k)`. Its index inequality is valid because
`Y>=k`. All displayed congruences are encoded as differences of two
natural quotient variables, so signed quotients cause no restriction.
The remaining strict/non-strict inequalities have natural slacks.
Consequently the entire positive-power graph has a natural witness at
every common bound `W>=n,k`, and specifically at `W=n+k`.

The construction above is the forward proof of Mathlib's
`Pell.eq_pow_of_pell`, with `W` arbitrary instead of `max n k`.
Its original proof uses `max` only to obtain `n<=W`, `k<=W` and `W>0`.
Source inspected inertly, without running Lean:

* `Mathlib/NumberTheory/PellMatiyasevic.lean`, theorem
  `eq_pow_of_pell`, lines 865--911 in the pinned checkout, SHA256
  `a8ea2ddf5167a9163f3af19309eed96213848b632b58f8e5857535b3a1412341`.
* `DiophantineConsistency/PowerRepresentation.lean`,
  `criterion_iff_pow`, SHA256
  `6d8f1dce54132c6824e25d195bb888baf71553e4985183b806ef03e95d2a90b4`.
* `DiophantineConsistency/PellRepresentation.lean`,
  `criterion_iff_pell`, SHA256
  `28389a7a799897bf7f2a82f2965e58b14bfc37093ef3751891462e6e72aa1bd8`.

The underlying indexed-Pell theorem is retained, not replaced by finite
testing. The new universal step is that its outer power construction
works at every common bound, as proved above.

## 2. Soundness and the ordinary-subtraction boundary

Take a zero of the modified positive-power rows with `n,k>0`. Set
`W=n+k`, and restore the deleted natural slacks by `wn=k,wk=n`.
Every original positive-power row is then satisfied. The original
soundness criterion gives `m=n^k`.

The compiler encodes the power congruence as
`X+Y*n=Y*A+m mod T`, with ordinary integer arithmetic. To match the
criterion's natural subtraction `A-n`, its parent proof requires
`A>W>=n`. This implication still holds before applying power soundness:
the last norm is

```
A^2=1+W^3*(W+2)*Z^2,
```

and `A>=2,W>=1`. Thus `Z` cannot be zero, and `A^2>W^2`, so `A>W`.
No assumption about the unknown output `m` or any later CRT row enters
this argument.

The static positivity induction for all 55 actual calls is unchanged.
All inputs are positive on every full natural zero; this candidate
does not delete zero-case guards from a graph called with arbitrary
inputs. The copied checker also tests the generic zero branches, but
they are absent from the emitted positive-specialized equation.

## 3. Whole direct certificate equivalence

Keep the frozen `shared-crt-prime-lift` construction, its independent
private bounds, prime-supported CRT columns and named C222-to-refutation
calibration. Only the `Builder.power` common-bound allocation changes.

From a new zero, restore the three deleted coordinates of each call as
above, in topological call order. This gives a zero of the old graph
with the same base, exponent and output values. Conversely, starting
from a valid outer direct certificate, reconstruct each arithmetic
macro in order. At every positive-power call, Section 1 supplies fresh
witnesses with `W=n+k`. The power output remains its actual `n^k`;
later arithmetic inputs therefore retain their intended values.
Recompute all definitional gates, including the affine gates eliminated
from the final equation. Nonnegative affine restoration preserves
natural existence and degree two of the residuals.

This proves natural-zero existence equivalent to the frozen prime-lift
candidate, and hence to its explicitly inherited refutation predicate.
It does not prove that any zero exists, prove Con(ZFC), or emit an
internal derivation in the encoded object-ZFC calculus.

## 4. Literal results and finite checks

The reproducible generator authenticates all seven complete frozen
parent source files before applying its recorded exact patches. The
source predicate, calculus, binomial and factorial formulas, prime-lift
bound, exporter and actual numerical C222 target are unchanged.

| Equation | Natural variables | Quadratic rows | Quartic terms | Height |
|---|---:|---:|---:|---:|
| Frozen prime-lift affine | 3,609 | 2,949 | 15,752 | 127,285,349 |
| Fixed-bound affine | **3,443** | **2,838** | 15,754 | 127,302,193 |
| Frozen prime-lift retained | 6,180 | 5,520 | 17,421 | 1,992 |
| Fixed-bound retained | **5,960** | **5,355** | **16,894** | **1,992** |

All four have exact degree four. The affine change saves 166 variables
and 111 rows, while adding two expanded monomials and slightly raising
height. This is a variable reduction, not a claim to dominate every
metric. The retained version improves variables, rows and terms at
the same height. Its 220-variable saving is 165 semantic coordinates
plus a net 55 gate coordinates; the removed bound rows also remove
their two formerly necessary addition gates per call. Shared gates
and support-capped affine substitution account for the different
affine total. Exact exported row identity checks establish the counts.

Each isolated positive-power graph now has 24 certificate coordinates
and 15 non-definitional constraints, instead of 27 and 17. Its exact
symbolic gate-substitution audit verifies all 15 polynomials, including
the rearranged last norm. All 55 actual calls have distinct ordered
base/exponent atom pairs; memoization therefore gives no further
equal-ID sharing. Every variable of both emitted quartics occurs.

The checker recomputes the complete squared-residual polynomial,
authenticates the source patch, checks the arbitrary-bound Pell
construction on finite controls, and runs the adapted arithmetic,
positivity, affine-restoration and exact power-identity auditors in
both normal and optimized Python. Finite controls support the literal
transcription; Sections 1--3 establish the unbounded arithmetic claim.
