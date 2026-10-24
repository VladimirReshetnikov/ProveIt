# Delayed power-quotient signs: an explicit quartic in 780 integers

## 1. Statement and exact object

Let `r_0,...,r_433` be the 434 literal quadratic residuals in
`equations/equation.json`, in its declared order of 780 coordinates. Define

\[
P_{780}(x_0,\ldots,x_{779})=\sum_{j=0}^{433}r_j(x)^2.
\]

Every coordinate is an unrestricted integer. There are no implicit
inequalities, divisibility conditions, variable exponents, or coefficient
parameters. `equations/expanded_polynomial.json` is the complete collected
polynomial: 9,628 nonzero monomials, exact degree 4, maximum absolute
coefficient 2,445,790,974,704. Its byte SHA-256 is
`45a5f432474ccbefa050b8c4d95059c8587f0697789c0f1209df2cdd3b558a8e`.
The coefficient of `x_0^4` is 3, certifying that the degree is exactly 4.

The new theorem proved here is an exact existence equivalence between this
integer polynomial and the pinned 690-variable natural source. Composing
with that source's stated arithmetic and logical calibration gives

\[
\mathrm{ZFC}\vdash
 (\exists x\in\mathbb Z^{780}\;P_{780}(x)=0)
 \longleftrightarrow \neg\operatorname{Con}(\mathrm{ZFC}).
\]

Negating both sides gives the requested nonexistence formulation. This is
an ordinary mathematical proof formalizable in ZFC. The finite checker
certifies the literal algebraic instance and proof premises; it is not a
new Lean proof or an emitted object-language ZFC proof.

## 2. Frozen source and inherited theorem

The immediate source is `ConZFC_407_888_Quartics_2026-10-24.zip`, stored in
ProveIt at commit `ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`, path
`docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip`. Its SHA-256 is
`59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59`, and its
Git blob identifier is `6766039023a30d605132158a12ee7488264b2049`.
The entire archive is retained in `upstream/`; its notices are preserved.
`SOURCE_PINS.json` also authenticates the thirteen extracted files used by
this construction against their exact archive members.

Write `S(y)=0` for all 606 quadratic residuals of the archive's
`equations/source690/equation.json`, copied verbatim to
`upstream/source690/equation.json`. Its intended domain is
`y in N^690`, with zero included. The inherited theorem is

\[
\exists y\in\mathbb N^{690}\ S(y)=0
\quad\longleftrightarrow\quad C_{222}(1)
\quad\longleftrightarrow\quad
\exists p\;\operatorname{Prf}_{\mathrm{ZFC}}(p,\bot).
\]

The immediate archive's report and proofs establish the arithmetic
reduction. They identify `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` as the inherited
logical calibration, pinned there to
`08200eb10fde2db408c69dffd840d6920a569b1f`. The complete Lean dependency
closure is not supplied by this new component. This construction uses the
same numerical calculus and does not introduce a Turing-machine or
universal-polynomial encoding.

The raw source ledger has 1,301 coordinates and 1,217 rows. Exactly 611
raw rows become zero identities after restoring the source's eliminated
monotone gates; the other 606 become the literal rows of `S`. The checker
verifies these identities by exact integer polynomial arithmetic. Thus
the raw semantic interface used below holds at every **integer** zero of
`S`, even before signs have been recovered. Omitted raw coordinates are
restored by their monic polynomial definitions, not by assuming they are
natural.

## 3. Why the sign proof can be postponed

The parent integer conversion guarded 167 of the 690 coordinates using
three private integer witnesses per guard. It derived the other 523
coordinate signs from the equations, then made signed monic
substitutions. Here only 131 guards are retained. The main saving comes
from proving the signs of the 23 private power-congruence quotients
**after** proving the exponentiation graphs correct.

No new identity for Pell sequences is claimed. The contribution is its
use as a delayed sign certificate: the defining congruence does not need
the quotient's sign for soundness, while the exact recurrence recovers
that sign once the value is known. The shared frame and all index tests
are checked before any such sign is used.

For each retained guard coordinate `y_v` impose

\[
y_v=a_v^2+b_v^2+c_v(c_v+1),\qquad a_v,b_v,c_v\in\mathbb Z. \tag{G}
\]

This forces `y_v>=0`, since the product of two consecutive integers is
nonnegative. Conversely every nonnegative integer has this form. Indeed,
Legendre's three-square theorem represents `4y_v+1` by three squares; its
residue modulo 4 forces one square odd and the other two even. Writing
them as `(2c_v+1)^2,(2a_v)^2,(2b_v)^2` gives (G).

The elementary sign rule used between semantic stages is as follows.
An existing row, up to sign, is factored exactly as

\[
a(\widehat y)y_v-b(\widehat y)=0,
\]

where neither polynomial involves `y_v`. If established facts show
`a>=1` and `b>=0`, then `y_v>=0`; if also `b>=1`, integrality gives
`y_v>=1`. The certificate permits nonnegative sums of monomials whose
odd-power factors already have nonnegative signs. A monomial whose
factors all have established lower bound 1 also contributes its positive
coefficient to a constant lower bound. This allows, for example, a
negative constant to be outweighed by a known positive monomial. Exact
affine-square right sides are another permitted nonnegative form.
Each inference is checked in its given order. No row can prove its own
premise by a circular sign assumption.

Starting only with the 131 guards, these elementary rules prove 623 of
the 690 source coordinates nonnegative. They also prove the strict
positivity facts needed next, including **all nine bases** and **all
exponents**. In particular, positivity of a factorial output used as a
power base is proved from literal arithmetic rows; factorial semantics
are not invoked first.

## 4. The dominating frame has no quotient-sign premise

For each of the 23 calls, denote its base, exponent and proposed output
by `n,k,m`. There are 47 distinct raw atoms in the union of these triples.
The exact shared frame is

\[
W=2+\sum_{a\in\mathcal A}a,\qquad Z=z+1,\qquad
A^2-W^3(W+2)Z^2=1. \tag{F}
\]

At the first stage all atoms in the sum are already nonnegative,
`n,k>=1`, `A>=0` and `Z>=1`. The sum is over distinct source atoms,
not over occurrences; relationships between named atoms are preserved
by their gate equations. The checker authenticates (F) against the raw
ledger, including those relationships.

We obtain `W>=2`, `1<=n,k<=W`, `0<=m<=W`, and `A>W^2`.
Rewrite the norm as

\[
A^2-((W+1)^2-1)(WZ)^2=1.
\]

For an integer base `a>=2`, let the natural Pell coordinates satisfy

\[
X_0(a)=1,\quad Y_0(a)=0,\qquad
X_{j+1}(a)=aX_j(a)+(a^2-1)Y_j(a),\quad
Y_{j+1}(a)=X_j(a)+aY_j(a).
\]

The standard classification of positive Pell solutions gives
`A=X_j(W+1)`, `WZ=Y_j(W+1)` for some `j>0`. The recurrence modulo `W`
gives `X_j(W+1)=1 mod W` and `Y_j(W+1)=j mod W`. Hence `W|j` and
`j>=W`. Consequently

\[
A\ge(W+1)^j\ge(W+1)^W>W^W\ge n^k. \tag{B1}
\]

The nine modulus equations and the discriminant equation are exactly

\[
T_n=2An-n^2-1,\qquad D=A^2-1. \tag{T}
\]

They have not been assigned nonnegative guards. Because `1<=n<=W<A`,
the quadratic `2An-n^2-1` is increasing on this integer interval. Thus

\[
T_n\ge 2A-2>W^W\ge n^k,
\qquad T_n>W\ge m,\qquad D\ge1. \tag{B2}
\]

This proves all ten missing frame signs independently of any power
quotient. Repeating the elementary sign rules now proves 644 source
coordinates nonnegative.

## 5. All Pell indices are identified before power quotients

There are 15 seed exponents `k_i`, and three further exponents derived
by shifts 1 or 2. For each seed the raw system contains

\[
\begin{aligned}
Y_i&=k_i+e_i, &X_i^2-(A^2-1)Y_i^2&=1,\\
S_i^2-(B^2-1)R_i^2&=1, &S_i&=X_i+Us_i,\\
R_i&=k_i+4Y_i r_i.
\end{aligned}\tag{I1}
\]

The shared auxiliary equations are

\[
\begin{aligned}
U^2-(A^2-1)V^2&=1, &B&=A+Ub,\\
V&=\left(\prod_{i=1}^{15}Y_i^2\right)(v+1),
&B&=1+4V(q+1).
\end{aligned}\tag{I2}
\]

At this stage the checker verifies, by the already established signs of
the exact restored expressions, that every witness in (I1) and (I2) is
nonnegative and `k_i>=1`. Therefore `Y_i>=1`, `V>=1`, `B>=5`,
`Y_i^2|V`, and `4Y_i|(B-1)`. Each seed is an instance of the inherited
Matiyasevich Pell-index criterion
`DiophantineConsistency.PellRepresentation.criterion_iff_pell`.
It gives

\[
X_i=X_{k_i}(A),\qquad Y_i=Y_{k_i}(A). \tag{I3}
\]

For the three derived pairs, the exact addition identities are

\[
X_{k+s}=X_kX_s+DY_kY_s,\qquad
Y_{k+s}=X_kY_s+Y_kX_s,
\]

where `s=1` uses `(X_s,Y_s)=(A,1)` and `s=2` uses
`(X_s,Y_s)=(2D+1,2A)`. Their polynomial gates and exponent-shift
identities are checked literally. Thus all 18 distinct required pairs
are known true before a sign is inferred for any power quotient.

## 6. The signed quotient lemma

Fix a call with the already proved conditions
`n,k>=1`, `0<=m<T`, `n^k<T`, `T=2An-n^2-1>0` and the true Pell pair
`X=X_k(A),Y=Y_k(A)`. Its remaining equation is

\[
X+nY=AY+m+Th,\qquad h\in\mathbb Z. \tag{P}
\]

Set `H_j=X_j(A)-(A-n)Y_j(A)`. Direct substitution into the two
Pell recurrences proves

\[
H_0=1,\qquad H_{j+1}=nH_j+TY_j(A).
\]

Induction, equivalently unrolling this first-order recurrence, yields

\[
H_k=n^k+T\sum_{j=0}^{k-1}n^{k-1-j}Y_j(A). \tag{R}
\]

Equations (P) and (R) imply `m=n^k mod T`. The two values both lie
in `[0,T)`, so `m=n^k` as integers. Subtract this equality from the
same equations and cancel the positive integer `T` to get

\[
h=\sum_{j=0}^{k-1}n^{k-1-j}Y_j(A)\ge0. \tag{H}
\]

The congruence argument never used `h>=0`. Its sign is a consequence
of exact exponentiation and the recurrence, which is why its private
guard is unnecessary. Apply this argument separately to all 23 calls.
It supplies 23 signs, and the elementary row rules supply the remaining
23 product signs. Every one of the 690 original source coordinates is
now nonnegative.

The order is essential: retained guards; elementary signs; frame bounds;
remaining elementary signs and all Pell index tests; exact powers;
power quotient signs; remaining elementary signs. The certificate and
checker follow this order rather than treating all signs as simultaneous
assumptions.

## 7. Exact guarded-system equivalence and projection

Let `G_131` consist of the 606 source rows and the 131 rows (G), all
over unrestricted integers. It has 1,083 coordinates and 737 rows.
At any integer zero of `G_131`, Sections 3--6 prove that the first 690
coordinates are natural; since the source rows are unchanged, they form
a natural zero of `S`. Conversely any natural zero of `S` extends to
an integer zero of `G_131` by the independent three-square constructions
for the 131 guards. Hence

\[
\exists y\in\mathbb N^{690}\ S(y)=0
\quad\longleftrightarrow\quad
\exists z\in\mathbb Z^{1083}\ G_{131}(z)=0. \tag{E1}
\]

Next a row `z_v-f=0`, or its negative, is selected with `f` an integer
polynomial not involving `z_v`. Substitute `z_v=f` everywhere and delete
that row and coordinate. Projection and restoration are mutually inverse
between the solution sets: a reduced zero restores uniquely by the same
identity. Neither sign nor divisibility conditions are needed because
all coordinates here range over the integers. The independent checker
expands every substitution, verifies that remaining rows stay quadratic,
and reconstructs the complete coefficient lists.

There are 303 such eliminations: 188 affine and 115 quadratic. No
unconstrained coordinates are discarded. Reverse traversal therefore
uniquely restores the full 1,083-coordinate solution from a target zero.
This leaves 780 coordinates and 434 quadratic rows. A sum of squares
vanishes over the integers precisely when every summand vanishes, so

\[
\exists z\in\mathbb Z^{1083}\ G_{131}(z)=0
\quad\longleftrightarrow\quad
\exists x\in\mathbb Z^{780}\ P_{780}(x)=0. \tag{E2}
\]

The converse natural-to-guarded extension is existential and need not be
unique; uniqueness is asserted only for the signed monic projection.
Combining (E1), (E2), and the inherited source theorem proves Section 1.

## 8. Exact savings and scope of verification

| Quantity | Parent integer888 | This integer780 |
|---|---:|---:|
| Independent nonnegative guards | 167 | 131 |
| Signed source coordinates | 1,191 | 1,083 |
| Signed source rows | 773 | 737 |
| Monic eliminations | 303 | 303 |
| Final integer variables | 888 | 780 |
| Quadratic residuals | 470 | 434 |
| Collected monomials | 10,156 | 9,628 |
| Exact degree | 4 | 4 |
| Maximum absolute expanded coefficient | 2,445,790,974,704 | 2,445,790,974,704 |

The 36 removed guards are the 23 private power quotients, nine base
moduli, `D`, and three coordinates handled by the stronger elementary
factor rule: `endpoint.ut`, `factorial0.output`, and
`crt.nonnegative_quotient`. All source indices and names appear in
`certificates/guard_changes.json`. The reduction saves 108 integer
variables (12.16%) and 528 monomials relative to this immediate parent.
This is a specific improvement within the direct C222 quartic family;
other repository equations have many fewer variables at a different
degree or coefficient-size cost. No absolute or global minimality or
worldwide novelty claim is made.

`check.py` imports neither the producer nor its elimination module. It
checks frozen source bytes, all raw-to-source identities, all ordered
sign premises, the complete frame/index/power interface, the exact
integer guard lift, every inverse substitution, the fully collected
single polynomial, and the numerical metrics. It uses explicit checks
rather than `assert`, so Python optimization cannot remove its checks.
`verify.py` adds isolated byte-for-byte reproduction and deliberately
corrupted certificates that must be rejected. These are finite checks
of a fixed instance. The unbounded Pell classification, Pell-index
theorem, three-square theorem, and source calibration remain the
mathematical dependencies stated above.

All new arguments use integer polynomial identities, induction, elementary
order and divisibility, and the stated classical arithmetic theorems.
They can be interpreted in ZFC's internal integers without assuming
Con(ZFC) or arithmetic soundness. They establish an equivalence; they do
not decide whether the equation has a solution.
