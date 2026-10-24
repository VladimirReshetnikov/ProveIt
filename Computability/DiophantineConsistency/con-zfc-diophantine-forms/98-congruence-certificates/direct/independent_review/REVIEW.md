# Independent review: oriented positive-power graph and direct quartic

## Verdict and scope

The final eleven-auxiliary positive-power graph is sound and complete over
nonnegative integers for every pair of strictly positive input integers
n,k. The four oriented quotient replacements and the fixed choice W=n+k
are justified. The subsequent exact coordinate eliminations of X, S and R are also valid. No new gap was found in those changes.

The exported direct equation independently checks as a sum of squares of
2,089 quadratic residuals in 2,473 nonnegative integer variables, with
20,580 collected monomials, exact degree four, and maximum absolute
coefficient 127,808,289. The exact residual expansion, all variable indices,
every declared variable's occurrence, source-file pins, and all 55 power
block censuses pass in normal and Python -O modes. The checker imports no
author builder or polynomial-arithmetic library.

The second export, retaining the affine wires, also passes the same full
independent checks. Its exact census is 4,860 natural variables, 4,476
quadratic residuals, 14,719 monomials, degree four, and coefficient height
1,837. Every residual coefficient has absolute value at most four. The
same graph proof applies; it uses more variables and smaller coefficients.

Reproduction from this component's directory:

```
python3 independent_review/check_export.py eq
python3 -O independent_review/check_export.py eq
python3 independent_review/check_export.py small_height
python3 -O independent_review/check_export.py small_height
```

This review certifies the new graph argument and finite export algebra.
It does not independently reprove the inherited C222 calculus calibration,
the CRT packing theorem, or their internal interpretation in ZFC.

## Reviewed primary and repository sources

* The locally supplied `upstream/PellMatiyasevic.lean`, pinned by the author
  to mathlib commit 81a5d257c8e410db227a6665ed08f64fea08e997, is SHA256
  a8ea2ddf5167a9163f3af19309eed96213848b632b58f8e5857535b3a1412341.
* Its `matiyasevic` theorem gives the exact finite Pell-coordinate criterion.
* Its `eq_pow_of_pell` theorem gives the exponentiation criterion, including
  the final Pell equation, n<=W, k<=W, and output<T.
* The repository wrappers `PellRepresentation.lean` and
  `PowerRepresentation.lean` explicitly translate integer norm residuals
  and natural-subtraction conventions into those criteria.
* The reviewed new method is `Builder.power_oriented`; the generic norm
  emitter uses X²+Y²=1+A²Y², exactly the desired integer norm equation.

## 1. An intermediate fourteen-auxiliary graph

For n,k>0 and natural m, use fourteen natural auxiliaries

```
A,X,U,S,R,z0,y0,q0,d0,gap,qB,qS,qR,qX.
```

Define Z=z0+1, Y=k+y0, W=n+k, T=m+gap+1,
V=Y²(d0+1), B=1+4Y(q0+1). There are four norm equations

```
X²-(A²-1)Y²=1,
U²-(A²-1)V²=1,
S²-(B²-1)R²=1,
A²-((W+1)²-1)(WZ)²=1,
```

and five other equalities

```
B=A+UqB,  S=X+UqS,  R=k+4YqR,
X+Yn=YA+m+TqX,  2An=T+n²+1.
```

The output m is not counted among the fourteen auxiliaries. Every displayed
defined value is implemented by nonnegative arithmetic gates before the
final affine eliminations.

## 2. Soundness and the subtraction convention

W>=2 and Z>=1. The last norm implies A²>W², hence A>W>=n and A>1.
Thus the expression A-n appearing in mathlib is an ordinary nonnegative
difference here; no truncated-subtraction discrepancy is possible.

The definitions give Y>=k>0, V>0, Y²|V, B>1, B=1 modulo4Y, and T>m.
The three oriented congruence equations imply the exact corresponding
modular hypotheses of `matiyasevic`. Its zero-ordinate branch is impossible
because k>0. Consequently X and Y are the Pell coordinates at index k
for parameter A.

The fourth oriented equality rearranges to
`X=Y(A-n)+m (mod T)`. Together with `2An=T+n²+1`, T>m, W>=n,k,
and the last norm, these are precisely the positive-input branch of
`eq_pow_of_pell`. Hence m=n^k.

## 3. Completeness with W=n+k

The mathlib completeness proof sets W=max(n,k), but uses that definition
only through W>0, n<=W and k<=W. It then sets

```
A=chi_(W+1)(W),  Z=psi_(W+1)(W)/W.
```

The recurrence modulo W shows W divides psi_(W+1)(W), so Z is natural.
Moreover psi_(W+1)(W)>=W>0, hence Z>=1. Its Pell equation is exactly the
last norm above. The estimates used in the proof remain valid for every
W>=n,k with W>0:

```
n^k <= n^W < (W+1)^W <= A.
```

Thus W=n+k is permitted before any Pell witnesses are chosen. In
particular the proof does not need freedom to increase W later.

The same proof constructs positive T=2An-n²-1>m and the power congruence.
The `matiyasevic` completeness theorem supplies natural U,V,S,R,B with
V>0, Y²|V, B>1 and the required congruences. Since Y>=k>0, this gives
the nonnegative slacks y0=Y-k, d0=V/Y²-1, q0=(B-1)/(4Y)-1,
gap=T-m-1, and z0=Z-1. The only remaining issue is the signs of the
four congruence quotients; those signs are proved next.

## 4. Four nonnegative quotient proofs

First, V is a positive multiple of Y², so V>=Y²>=Y>=1.
The first two norms consequently give U>=X and U>=A.
Also X>=A>1, B>1, and S>=1.

If B is a positive representative of A modulo U, with 0<A<=U, then
B>=A: otherwise 0<A-B<U would be a nonzero multiple of U. This also
handles U=A, when the least positive representative is U. Therefore
qB=(B-A)/U is natural.

Exactly the same argument with 0<X<=U and S>=1 gives S>=X and natural
qS=(S-X)/U. Since 0<k<=Y<4Y and R is natural with R=k modulo4Y, R>=k,
so qR=(R-k)/(4Y) is natural.

For the power quotient, the first norm gives

```
X²-(A-1)²Y² = (2A-2)Y²+1 >0,
```

so X>(A-1)Y. Let D=X+Yn-YA-m. Then

```
D > Y(n-1)-m >= -m > -T.
```

D is an integral multiple of positive T by the old congruence. Any negative
multiple would be <=-T, impossible. Thus D>=0 and qX=D/T is natural.
These four arguments prove that the new directed equalities retain every
completeness witness up to choosing the unique quotient, rather than only
some favorable sample witnesses.

## 4a. Exact elimination to the final eleven-auxiliary graph

In the intermediate graph A>W>=n, so a0=A-n-1 is a natural number.
Its oriented power equality is precisely

```
X=Y(a0+1)+m+TqX.
```

Consequently replace the primitive A by a0 with A=n+a0+1 and define
X by that displayed nonnegative polynomial. Define S=X+UqS and
R=k+4YqR as nonnegative polynomials too. The three corresponding directed
equalities become identities and are deleted. The remaining auxiliaries
are exactly U,a0,z0,y0,q0,d0,gap,qB,qS,qR,qX, eleven in total; the
remaining constraints are the four norms, B=A+UqB and 2An=T+n²+1.

Every intermediate graph solution has a unique projected assignment to
these coordinates, and every final solution restores X,S,R,A by their
literal definitions. The two maps are inverse. In particular this is an
exact coordinate elimination, not a further number-theoretic assumption
or a restriction on the Pell witnesses. All restored coordinates are
nonnegative before any remaining constraint is used. The proof above
therefore applies to the final eleven-auxiliary graph.

## 5. Positive-input specialization in the complete construction

The complete builder introduces t=t0+1 and m=m0+1. Its first power has
base m+1 and exponent t. Every range-binomial input is an encoded
coordinate plus one and has lower argument a bound plus one. The other
binomial calls have positive first and second arguments by construction.
The factorial argument H is a sum with an added one; the nested factorial
uses a positive shifted base and positive exponent. The moduli-product
power with base T is licensed after the factorial graph gives T=H!>=1.
Thus the power-call dependencies are acyclic and every power macro is
invoked on positive inputs at a zero of the complete system. One must
retain this dependency argument; the reduced graph is not being asserted
to represent zero-base or zero-exponent cases.

## 6. Gate elimination and the final equation

The arithmetic gates are triangular additions and multiplications of
natural quantities. The exporter eliminates only a monic affine defining
equation whose restored expression has nonnegative coefficients and
references earlier coordinates. Substitution is therefore a bijective
elimination of a uniquely determined natural gate value. The support cap
of four affects size, not correctness. Unused definitional gates can also
be restored in triangular order without adding a new condition.

All remaining residuals have degree at most two. Over integers, a finite
sum of their squares vanishes exactly when every residual vanishes. The
independent checker reconstructs that entire sum and matches every
coefficient in `expanded_polynomial.json`, rather than relying on random
evaluations or the builder's reported counts.

Each of the 55 final power blocks has exactly six semantic constraint
labels (the four norms, B_mod_U and T_definition), once each, and exactly
twelve primitive natural coordinates including its output. Every one of
the 2,473 declared variables occurs. The quartic and all 20,580 expanded coefficients are
fully materialized.

## Limits

The new graph proof is ordinary mathematics, formalizable in elementary
number theory; no new Lean theorem was compiled here. The independent
finite checks do not prove the inherited C222/ZFC calibration or the
unbounded CRT packing theorem. The new equation improves the inspected
direct route's variable count; its monomial count is larger than the
previous 3,614-variable direct equation's. It does not dominate the
low-variable native/Pell constructions on all measures.
