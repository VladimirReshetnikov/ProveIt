# Independent review of delayed power-quotient signs

This review covers the new transition from the pinned 690-natural-variable
source to the 780-integer-variable quartic. It examines the sign-recovery
order, the frame and index premises, the recurrence that recovers the signs
of the power quotients, and the subsequent signed coordinate eliminations.
The C222/refutation calibration of the original source is inherited rather
than re-proved by this review.

## 1. The central lemma is valid without a sign on h

Fix integers `A,n,k,m,T,h` with `A>=2`, `n,k>=1`, and
`0<=m<T`, `0<=n^k<T`. Suppose the certified Pell pair is
`X=X_k(A), Y=Y_k(A)` and

```
T = 2An-n^2-1 > 0,
X+nY = AY+m+Th.
```

Define `H_j=X_j(A)-(A-n)Y_j(A)`. The Pell recurrences give the exact
identities

```
H_0 = 1,
H_(j+1) = n H_j + T Y_j(A),
H_k-n^k = T sum_(j=0..k-1) n^(k-1-j) Y_j(A).
```

The displayed polynomial equation first implies `m=n^k modulo T`, even
when h is negative. The two bounds then force `m=n^k` as integers. Since
`T!=0`, substituting this equality proves that h equals the displayed
finite sum, hence `h>=0`. The sign is a consequence of already recovered
power semantics. It is not a premise for the congruence argument.

No assertion about the sign of `A-n`, or of the difference defining H,
is used. The conclusion also covers `k=1`, for which h is zero. The
finite-sum identity follows by natural induction, and is valid uniformly
in ZFC's internal natural numbers.

## 2. Frame bounds are recovered before any h sign

The certificate establishes nonnegativity of every semantic base,
exponent, and output atom before using the frame. Bases and exponents
are strictly positive. It separately establishes `A>=0` and `Z>=1`.
The frame identity is

```
W = 2 + sum(distinct semantic atoms),
A^2-W^3(W+2)Z^2=1.
```

Therefore `W>=2`, every power call has `1<=n,k<=W`, `0<=m<=W`,
and `A>W^2`. In particular `D=A^2-1>0`. For each stored modulus
`T_n=2An-n^2-1`, the estimate

```
T_n >= 2A-W^2-1 > W^2-1 >= W
```

already proves positivity, without assuming that modulus natural in
advance. Elementary sign propagation may then use these new facts.

For the stronger bound, rewrite the frame norm at Pell base `W+1`:

```
A^2-((W+1)^2-1)(WZ)^2=1.
```

Because `A>=0` and `WZ>0`, Pell classification gives
`A=X_j(W+1)`, `WZ=Y_j(W+1)` for a positive j. Reducing the recurrences
modulo W gives `Y_j(W+1)=j modulo W`, hence `j>=W`. Thus

```
A >= (W+1)^W > W^W >= n^k.
```

On `1<=n<=W<A`, the function `2An-n^2-1` is increasing, so
`T_n>=2A-2>W^W>=n^k`. Both m and the true power are in `[0,T_n)`.
These bounds depend only on the guarded and already propagated signs,
not on the intended correctness of any power output. Including proposed
power outputs in W therefore causes no circularity.

## 3. The required index witnesses stay natural until their use

The finite checker independently binds the literal interface to every
premise of `PellRepresentation.criterion_iff_pell`, inspected in the
pinned repository's `PellRepresentation.lean`. Before power recovery,
it has checked signs for every seed index k and for X,Y,S,R and their
bound and congruence quotients, together with the common U,V,B and
common product quotients. The equations give

```
Y=k+e,                    X^2-(A^2-1)Y^2=1,
U^2-(A^2-1)V^2=1,        S^2-(B^2-1)R^2=1,
V=(product_i Y_i^2)(v+1), B=1+4V(q+1),
B=A+Ub,                  S=X+Us,         R=k+4Yr.
```

Since `k>=1`, every Y is positive. The common product row consequently
implies `V>0`; the B row gives `B>1`. Divisibility by every `Y_i^2` and
the congruences required by the index criterion follow literally. This
identifies each seed pair as the intended Pell pair at its exponent.

The three derived pairs use acyclic addition by the fixed indices 1
or 2, with the exact polynomial Pell addition identities. Their correctness
does not use any unproved power-quotient sign. Every one of the 23 power
calls can then apply Section 1. The proposed power calls may depend on
each other's input/output atoms; the argument is pointwise simultaneous
and does not assume an earlier semantic evaluation of those calls.

## 4. Sign inference and signed restorations are sound

Each ordinary sign step is checked on an actual quadratic source row.
The checker isolates `a*x_v=b`, verifies `a>0`, and verifies `b>=0`
or `b>0` using only previously established signs and even powers.
Alternatively it verifies that b is exactly the square of an affine
integer polynomial and that a is a positive integer constant. These
are sound inference rules over unrestricted integers. The ordered
certificate prevents using a later sign prematurely.

Only the 131 guarded coordinates receive the standard representation
`x=a^2+b^2+c(c+1)`. It is nonnegative for all integers a,b,c, and
Legendre's three-square theorem gives a representation for every
nonnegative x. The new square variables are private to each guard.

After all 690 source coordinates have been proved nonnegative, the
guarded integer source is equivalent to the natural source. Subsequent
monic elimination is an integer-domain operation: a row `v-f=0` permits
exact substitution even when f has negative coefficients. Reverse order
restores all eliminated values. There is no requirement that an individual
restoring expression be visibly nonnegative; after the full integer
solution has been restored, the preceding sign theorem forces all
original source coordinates to be nonnegative. This ordering is valid
and avoids circular reasoning.

## 5. Independent finite checks and one corrected representation issue

The supplied `check.py` imports none of the generator, source compiler,
or elimination module. It authenticates the upstream ZIP and 13 extracted
members, expands all relevant raw gate identities, verifies each sign
inference, checks every semantic premise above, replays all 303 monic
substitutions, and compares the complete collected sum of squares with
the exported polynomial.

An initial structural comparison of the frame sum failed because the
raw semantic atom list includes both a and `a+2`; treating them as
independent cut variables leaves the difference `-(a+2)+a+2`.
The checker now reduces that difference by the already authenticated
topological monic gate identities. It checks an exact polynomial identity,
without a numerical sample or an assumed equality of unrelated atoms.
This resolves the representation issue and preserves the proof of every
atom's bound by W.

I ran the final checker with `python3 -O`, so checks could not depend
on Python assertions. The receipt is
`certificates/INDEPENDENT_CHECK.json`, with status PASS. It reports:

| Quantity | Verified value |
|---|---:|
| Natural source variables | 690 |
| Guarded coordinates | 131 |
| Nonnegative after initial propagation | 623 |
| Nonnegative after frame and middle propagation | 644 |
| Nonnegative after power recovery and final propagation | 690 |
| Positive power calls | 23 |
| Seed indices / derived indices / bases | 15 / 3 / 9 |
| Retained integer variables | 780 |
| Quadratic residuals | 434 |
| Collected monomials | 9,628 |
| Exact degree | 4 |
| Largest absolute coefficient | 2,445,790,974,704 |

The collected coefficient of `x_0^4` is 3, certifying the lower degree
bound. The upper degree bound follows from the exact quadratic residuals.

## 6. Scope of the conclusion

The new domain and projection transformations are proved as ordinary
integer arithmetic and Pell theory and are formalizable in ZFC. The
finite check establishes that the concrete supplied polynomials and
certificates satisfy the hypotheses of those arguments. The conclusion
preserves the parent's stated direct C222-to-syntactic-ZFC-refutation
equivalence. It does not independently re-prove that inherited source
calibration, prove Con(ZFC), produce a Lean kernel proof, or establish
global minimality among Diophantine equations.
