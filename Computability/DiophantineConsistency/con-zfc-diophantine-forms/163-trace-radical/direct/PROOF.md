# Proof of the new direct construction

## 1. Statements and dependencies

Write `Z` for the integers. Each selected endpoint is exactly the sum of
squares of its listed quadratic residuals. Consequently its zero set in
`Z^n` is the common zero set of those residuals. The immediate sources are
the fully explicit incoming factorial-free 241/242-coordinate equations
and shared-factorial-error 240-coordinate equation. Their ordinary
arithmetic/refutation proofs, source ledgers, finite transformations, and
logical-interface excerpts are retained under `inherited/`.

The shared-error endpoint changes no arithmetic semantics: Section 3
gives a sequence of bijections between its source's integer zeros and the
new 234-coordinate zeros. The self-power endpoints first replace the
factorial-free evaluation parameter by the one proved sufficient below,
and then use the same six bijective algebraic projections. This first
semantic replacement preserves existence of zeros through finite
refutations, and is not claimed to biject all old and new arithmetic
witnesses. Earlier inherited elimination of unused coordinates also
preserves existence rather than bijecting arbitrary unconstrained raw
assignments. The six new final projection steps each remove exactly their
one pivot and are genuine integer-zero-set bijections.

## 2. Proof-label authentication at F=t^t

Let `t>=2`. Let every label be an integer in `[0,t]`. Suppose an identity
of positive integers is of the form

    product_(i<t) (1+v_i F)
      = (1+F) product_(i<t) (1+p_i F)(1+q_i F),
    F=t^t.

The fixed extra factor on the right records the target label 1. Remove
the unit factors with label zero. Let the two remaining factor counts be
`r` and `s`. One side has at most `t` factors. If `r != s`, put
`m=min(r,s)`, so `m<=t`. The larger side is at least `(F+1)^(m+1)`;
the smaller is at most `(1+tF)^m < t^m(F+1)^m` when `m>0`, while the
case `m=0` is immediate. But `F+1>t^t>=t^m`, contradiction. Thus the
counts agree and both are at most `t`.

Replace the common evaluation point F by an indeterminate z. Each side
is now a product of `r<=t` factors `1+jz` with `1<=j<=t`. Its kth
coefficient `a_k`, for `0<=k<=r`, is a positive integer satisfying

    1 <= a_k <= binom(r,k)t^k <= t^r <= t^t=F.

For the middle inequality, put `m=r-k`: `binom(r,k)=binom(r,m)<=r^m<=t^m`.
Both polynomials have exactly the same range of nonzero degrees. Hence
each coefficient of their difference has absolute value at most `F-1`.
The constant difference is zero. If the difference polynomial were
nonzero, take its least nonzero coefficient `b_j`. Divide the equality at
F by `F^j` and reduce modulo F: it would imply `F|b_j`, contrary to
`0<|b_j|<F`. Thus the two polynomials coincide identically.

Unique factorization over the rationals, or the distinct roots `-1/j`,
now identifies every positive label multiplicity. It follows that label
1 has conclusion-minus-premise multiplicity one and every other positive
label has balance zero. This argument uses no claim that the evaluated
integers `1+jF` are pairwise coprime.

The inherited single-conclusion-flow argument converts this multiset
balance into a finite derivation. For completeness: take the closure of
truth under the finitely many certified rule instances. If target 1 is
outside, each rule with a conclusion outside has at least one premise
outside. Summing conclusions minus premises over outside labels is
therefore at most zero, whereas the proved multiplicity balance makes it
one. This contradiction yields derivability. Repeated premises and cyclic
rule multisets do not invalidate the argument.

### 2.1 Compatibility with the full factorial-free source

The parent uses `t=16+h^2`, `F=d^t`, and `d=2(t+1)`. The literal source
edit changes exactly its `growth.base_definition` residual to `d=t`.
In source storage `t0=t-16`, so the new residual is `d-t0-16`. Every
other residual and every witness-domain declaration is unchanged. The
same already present indexed Pell request at index t authenticates the
new positive base; no new power or index request is introduced.

The parent proof's remaining estimates continue to hold, with their
uses made explicit:

* `t>=16` gives `F=t^t>=16^16=2^64>2^32`, `F>=t`, `F>=7`, and
  `F>=t!>=lcm(1,...,t)`. Thus `R=F^2` satisfies the parent's generalized
  binomial-CRT radius hypothesis.
* The unchanged positive parametrizations `y=F(2v+1)^2` and
  `q=(2z+1)^2` give `y>=F>0` and `q>=1`. The old signed bootstrap,
  index row, two beta endpoints and power identities then give
  `x>=F+1` and `x>=2+(t+1)y`, without using a binomial interpretation
  prematurely. Consequently `q=|BH|^x>=2^x` and `|B|<q/2`.
* The factorial-binomial digit is still recovered from
  `(F^2+t)^t <= (F^2+F)^t <= 2^(t(F-1))`. The exponent gap against
  `q>=2^x`, with `x>=2+(t+1)F`, still bounds both its relevant
  coefficients and canonical low tail by the parent's `1/32` margin.
* The local derived-label bound uses `ell=2^22` and needs
  `ell(t+1)<x`. This follows from `F>ell` and the preceding endpoint
  bound. The complete local polynomial majorant `(2x)^(2^23)<2^x`
  uses only `x>2^32`, which is still satisfied.
* Every independent range coefficient remains bounded by `H^x`, and
  `q=B^x H^x` after the binomial sign is recovered. Thus the old
  normalized-remainder proof is unchanged. The boundary branch `y=F`
  is excluded exactly as in the parent by zero propagation from the
  initial beta accumulator to the final accumulator one.

For constructive completeness, choose h even and sufficiently large for
the finite proof. Then t is even, and

    v_2(F)=t*v_2(t)>=t>v_2(t!).

This supplies every 2-adic property formerly obtained from the even base
`2(t+1)`. If O is the odd part of t!, choose a sufficiently large odd
multiple w of O and set `y=Fw^2`. It is an even multiple of t!, is
cofinally large, and contains all pending accumulator values. Every beta
modulus `1+(i+1)y` is odd and pairwise coprime; the code x can therefore
be chosen even. The binomial `B=binom(F^2+t,t)` is odd because
`v_2(F^2)>floor(log_2(t))`, so the factors' valuations cancel those of
t! exactly. The existing parity choices of representatives yield odd H,
and `q=(BH)^x` is an odd square. The old common-root Pell completion is
applicable to the changed finite list of positive bases and the same
indices. This constructs all witnesses. Only completeness restricts h
to be even; soundness works for every algebraically allowed h.

All claims above compose with the retained parent CRT and Pell lemmas;
they do not replace those lemmas by a finite sampling argument.

## 3. Projection along a simultaneous quadratic radical

Let `f_1,...,f_m` be polynomials of degree at most two with integer
coefficients. Write `f_r=c_r+L_r+Q_r`, with homogeneous linear and
quadratic parts. Let `H_r` be the Hessian matrix of `Q_r`. Suppose an
integer vector d satisfies

    H_r d = 0 for every r.

Then the polynomial identity

    f_r(x+s d)=f_r(x)+s L_r(d)

holds in the independent variables x and s. Indeed the coefficient of s
from the quadratic part is `x^T H_r d=0`; its s-squared coefficient is
`Q_r(d)=d^T H_r d/2=0` in the integers. The division by two here is an
identity in characteristic zero, not a witness construction or a
division operation in the delivered equation.

Suppose some coordinate v of d is 1 and some row i has `L_i(d)=epsilon`
with `epsilon=1` or `-1`. Use coordinates z with

    old x_v = z_v,
    old x_w = z_w + d_w z_v  (w != v).

This is an integral triangular bijection, with inverse
`z_w=x_w-d_w x_v` and `z_v=x_v`. Every transformed residual contains
z_v only linearly, with constant coefficient `L_r(d)`. In particular
the ith residual is `epsilon*z_v+g(other z)`, where g has degree at
most two. Set `z_v=-epsilon*g`, substitute in every other row, and
delete the ith row and vth coordinate. The result remains quadratic,
because z_v occurred only linearly everywhere. The substitutions are
integral polynomials.

Forward projection sends each old common zero to a new one. Conversely
each new zero has the unique restored coordinate `z_v=-epsilon*g`,
followed by the unique inverse triangular transformation. These maps
are inverse polynomial maps on the integer zero sets. Thus existence of
zeros is preserved, without auxiliary sign assumptions or localization.

### 3.1 The six delivered steps

The certificate reindexes coordinates after each deletion and lists all
names, direction coefficients, pivot rows, explicit restorations, shears,
and retained coordinate maps. In historical source names the six common
directions are:

| Chosen pivot | Other nonzero direction coefficients |
|---|---|
| `mul.188` | `mul.194: -1` |
| `add.292` | `mul.303: -1` |
| `sqd.11` | `sqd.12: -1` |
| `add.71` | `mul.86: -2`, `add.83: -1` |
| `add.112` | `mul.123: -2`, `add.119: -1` |
| `add.277` | `mul.285: -2`, `mul.281: -1` |

The pivot coefficient is one in every row of this table. Source variable
names record provenance and are not a replacement for the actual
coefficient arrays. The independent checker confirms each complete
Hessian identity, each unit slope, both directions of every shear, every
monic relation, every resulting residual, and every collected coefficient.
Exactly one coordinate and one row are removed at each of the six steps.

### 3.2 A precise termination certificate

For each endpoint, stack all rows of the Hessians H_r into a single
integer matrix. Its column count is the number of coordinates. The
supplied modular Gaussian-elimination certificate has full column rank
over the field of 101 elements: ranks 234, 235, and 236 respectively.
Therefore a square minor of the integer matrix is nonzero modulo 101
and hence nonzero over the rationals. Its rational column rank is full,
so the simultaneous rational Hessian kernel is zero.

This proves only that this specific projection mechanism has no further
nonzero direction in the final charts. Nonlinear coordinate changes,
different row ideals, semantic arithmetic changes, and entirely different
proof calculi remain available. No global minimality conclusion follows.

## 4. Consistency equivalence and limits

The retained parent sources prove, by ordinary mathematics formalizable
in ZFC, that a zero exists exactly when a finite C222 derivation exists.
Section 2 preserves that equivalence for the self-power source. Section 3
preserves the integer zero sets of all three chosen inputs. The inherited
C222/ZF and ZF/ZFC syntactic-refutation calibrations therefore give

    ZFC proves: exists x in Z^n with P(x)=0 iff a finite ZFC refutation exists.

Negating yields the claimed equivalence between no integer zero and
Con(ZFC). It neither proves consistency nor finds a refutation. The new
finite checker certifies fixed polynomial data and algebraic identities;
it is not an end-to-end proof-assistant check of all inherited arithmetic
and formal-logical dependencies.

All new work is AI assisted. The retained notices credit C222, the
generalized binomial-CRT theorem, signed Pell authentication, normalized
remainders, shared factorial errors, affine exposure, and the earlier
exact projection checkers. The new measured contributions are the
self-power label bound, its valid source composition, and the simultaneous
quadratic-radical projections exhibited by these literal certificates.
