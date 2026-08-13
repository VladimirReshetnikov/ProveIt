# An exact improvement to `λ ≤ 4.5235` for Klarner's constant

**Date:** 12 August 2026

**Result:** `λ ≤ 9047/2000 = 4.5235`

**Previous bound:** `λ ≤ 4.5238` (Bui, arXiv:2511.00461v2)

**Numerical improvement:** `0.0003`

## 1. Statement and context

A fixed polyomino is a finite edge-connected set of cells in the square
lattice, counted up to translation.  Let `A(n)` be the number of fixed
polyominoes with `n` cells.  Klarner's constant is

\[
  \lambda=\lim_{n\to\infty} A(n)^{1/n}.
\]

Klarner's concatenation makes `A` supermultiplicative, so Fekete's lemma gives
both existence of the limit and

\[
  \lambda=\sup_{n\geq1} A(n)^{1/n}.
\]

The upper-bound history is unusually sparse.  Eden obtained `6.75`; Klarner
and Rivest successively obtained `5`, `4.83`, and `4.649551`; Barequet and
Shalah reached `4.5252` using over twenty-three trillion local configurations.
In May 2026, Bui replaced that enumeration by seventeen interacting local
neighborhood types and proved `λ ≤ 4.5238` with a small rational certificate.
The exact certificate below tightens that same proved recurrence system.

The public searches performed on 11 August 2026 and refreshed on 12 August
2026 found Bui's `4.5238` as the current claimed upper bound and found no
occurrence of `4.5235` in this context.  Thus the result appears to be new;
that search is evidence about novelty, not part of the mathematical proof.

## 2. Bui's geometric recurrence input

For each of seventeen required/forbidden square-lattice neighborhoods, Bui
counts marked occurrences in `n`-cell polyominoes.  Write the resulting
nonnegative sequences as

\[
 C,D,E,F,G,H,P,Q,R,S,T,U,V,W,X,Y,Z.
\]

The six one-cell states satisfy

\[
 C(1)=D(1)=E(1)=F(1)=G(1)=H(1)=1,
\]

and the other eleven states are zero at `n=1`; all states are set to zero at
nonpositive indices.  If

\[
 (AB)(n)=\sum_{\substack{i,j\geq1\\i+j=n}}A(i)B(j),\qquad
 (ABC)(n)=\sum_{\substack{i,j,k\geq1\\i+j+k=n}}A(i)B(j)C(k),
\]

Bui's Lemma 4 proves, for `n ≥ 2`,

\[
\begin{aligned}
C(n)&\le E(n-1),&D(n)&\le G(n-1),&E(n)&\le F(n-1),\\
F(n)&\le G(n)+P(n),&G(n)&\le E(n)+Q(n),&H(n)&\le D(n)+S(n),\\
P(n)&\le(EH+QD+XR+VY)(n)+(UYZ)(n),\\
Q(n)&\le G(n-1)+(GE)(n-1)+U(n-2)+(TG+RU)(n-2),\\
R(n)&\le Y(n)+W(n),\\
S(n)&\le G(n-1)+(EE)(n-1)+T(n-2)+(XG+YU)(n-2),\\
T(n)&\le X(n)+V(n),\\
U(n)&\le(DH+SD+YR+WY)(n)+(UZZ)(n),\\
V(n)&\le S(n-1)+(GG+TE+RT)(n-2),\\
W(n)&\le S(n-1)+(EG+XE+YT)(n-2),\\
X(n)&\le D(n-1)+G(n-2)+U(n-2),\\
Y(n)&\le C(n-1)+G(n-2)+T(n-2),\\
Z(n)&\le C(n-1)+E(n-2)+X(n-2).
\end{aligned}
\]

The southwest cell of every polyomino—bottommost, then leftmost—has no cell to
its left and no cell in the three positions in the row below.  This is exactly
a type-`G` occurrence.  Consequently

\[
  A(n)\leq G(n).
\]

In the formal development these sequences are definitions, not abstract
variables: each coefficient is the finite sum, over southwest-normalized
`n`-cell polyominoes, of the number of anchors at which the corresponding
required/forbidden pattern occurs.  The five same-size identities split an
occurrence set according to occupancy of one distinguished cell.  The `C`,
`D`, and `E` inequalities use injective deletion of a marked leaf.  The
remaining nine inequalities are proved by explicit finite maps from marked
source occurrences into disjoint sums of products of smaller marked
occurrences:

- `P`, `Q`, `S`, `U`, `V`, and `W` use the occupancy branches in Bui's
  Appendix B.  In each branch, prescribed nonempty connected seeds are grown
  into pairwise-disjoint connected territories covering the remainder.  The
  general `SeededPartition` theorem proves that such a partition exists when
  every remaining cell can reach a seed.  Each territory is normalized and
  oriented as its target neighborhood type; recovery lemmas undo those
  transformations and establish injectivity.
- `X`, `Y`, and `Z` split according to the two cells above the marked frame
  and use one- or two-cell deletion.  The maps retain a target mark and enough
  coordinate data to reconstruct both the deleted cells and the source
  occurrence.

Taking cardinalities of these injections produces exactly the two- and
three-fold convolutions in the displayed recurrences.  Thus the formal proof
uses Bui's geometric strategy unchanged, but the recurrence inequalities
themselves are discharged rather than assumed.

The coordinate source for this geometry is `Patterns.lean`, which contains
the seventeen finite required/forbidden offset tables.  Those tables were
manually checked entry by entry against the neighborhood diagrams on page 15
of Bui v2.  Lean's kernel verifies every later partition, deletion, recovery,
and counting argument relative to those coordinates; it does not itself
visually interpret the source PDF.  This is the ordinary human
source-transcription boundary of the formalization.

## 3. A finite weighted-prefix lemma

Fix `ζ > 0`.  For any one of the seventeen sequences put

\[
  \mathcal S_N=\sum_{1\leq n\leq N}S(n)\zeta^n,
\]

and collect the seventeen weighted prefixes in a profile
`b_N=(c_N,d_N,…,z_N)`.  All its coordinates are nonnegative and `b_0=0`.

Define the polynomial map `Φζ` by

\[
\begin{aligned}
\Phi_c&=\zeta+\zeta e,&
\Phi_d&=\zeta+\zeta g,&
\Phi_e&=\zeta+\zeta f,\\
\Phi_f&=g+p,&
\Phi_g&=e+q,&
\Phi_h&=d+s,\\
\Phi_p&=eh+qd+xr+vy+uyz,\\
\Phi_q&=\zeta g+\zeta ge+\zeta^2(u+tg+ru),\\
\Phi_r&=y+w,\\
\Phi_s&=\zeta g+\zeta e^2+\zeta^2(t+xg+yu),\\
\Phi_t&=x+v,\\
\Phi_u&=dh+sd+yr+wy+uz^2,\\
\Phi_v&=\zeta s+\zeta^2(g^2+te+rt),\\
\Phi_w&=\zeta s+\zeta^2(eg+xe+yt),\\
\Phi_x&=\zeta d+\zeta^2(g+u),\\
\Phi_y&=\zeta c+\zeta^2(g+t),\\
\Phi_z&=\zeta c+\zeta^2(e+x).
\end{aligned}
\]

Here is the finite form of the certificate argument.

**Weighted-prefix lemma.** If a nonnegative profile `a` satisfies
`Φζ(a) ≤ a` componentwise, then `b_N ≤ a` for every `N`.

**Proof.** Sum each coefficient recurrence only through `N+1`.  Every factor
index in a two- or three-fold convolution contributing in that range is at
most `N`.  Nonnegativity therefore lets us bound a truncated convolution by
the product of the corresponding prefixes through `N`.

Although Bui states Lemma 4 for `n≥2`, its displayed one-cell values extend
the encoded inequalities to `n=1`: the standalone `ζ` terms account for
`C(1),D(1),E(1)≤1`, and the remaining initial inequalities follow from the
six values equal to `1` and the eleven values equal to `0`.  Thus the finite
sum over `1≤n≤N+1` uses no unstated base case.

First compute the twelve coordinates

\[
 C,D,E,Q,S,V,W,X,Y,Z,P,U
\]

from `b_N` using the corresponding right sides of `Φζ`.  Then compute, in
this order,

\[
 G=E+Q,\quad F=G+P,\quad H=D+S,\quad T=X+V,\quad R=Y+W.
\]

Call the resulting topologically ordered profile `Advζ(b_N)`.  The summed
recurrences give

\[
  b_{N+1}\leq\operatorname{Adv}_\zeta(b_N).
\]

If `Φζ(a)≤a`, the first twelve coordinates of `Advζ(a)` are at most those of
`a`.  The five remaining inequalities then follow in the displayed order; for
example

\[
  g' = e'+q'\leq e+q=\Phi_g(a)\leq g,
\]

and

\[
  f'=g'+p'\leq g+p=\Phi_f(a)\leq f.
\]

Thus `Advζ(a)≤a`.  Since `b_0=0≤a`, induction on `N` proves `b_N≤a`.  This is
a finite-sum proof: indeed, all coefficients, `ζ`, and the coordinates of
`b_N` are nonnegative, so every coordinate polynomial in `Advζ` is monotone.
Consequently

\[
  b_N\leq a
  \quad\Longrightarrow\quad
  b_{N+1}\leq\operatorname{Adv}_\zeta(b_N)
  \leq\operatorname{Adv}_\zeta(a)\leq a.
\]

It assumes neither convergence nor a formal manipulation of infinite
generating functions. ∎

## 4. The new exact certificate

Set

\[
  \zeta=\frac{2000}{9047}=\frac1{4.5235}.
\]

In the coordinate order

\[
  (c,d,e,f,g,h,p,q,r,s,t,u,v,w,x,y,z),
\]

take `a` to have common denominator `10,000,000` and numerators

| coordinate | `c` | `d` | `e` | `f` | `g` | `h` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| numerator | 3482045 | 4310668 | 5751028 | 16014774 | 9499305 | 7394875 |

| coordinate | `p` | `q` | `r` | `s` | `t` | `u` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| numerator | 6515468 | 3748277 | 2390936 | 3084206 | 2902315 | 5050537 |

| coordinate | `v` | `w` | `x` | `y` | `z` |
| --- | ---: | ---: | ---: | ---: | ---: |
| numerator | 1238300 | 1015088 | 1664015 | 1375847 | 1132149 |

Direct rational subtraction gives the residual profile `a-Φζ(a)`:

| coordinate | exact residual |
| --- | ---: |
| `c` | `1023/18094000000` |
| `d` | `849/22617500000` |
| `e` | `579/22617500000` |
| `f` | `1/10000000` |
| `g` | `0` |
| `h` | `1/10000000` |
| `p` | `5231501455989/1000000000000000000000` |
| `q` | `19668376031/204620522500000000` |
| `r` | `1/10000000` |
| `s` | `11187866161/127887826562500000` |
| `t` | `0` |
| `u` | `46450875596063/1000000000000000000000` |
| `v` | `38974413/409241045000000` |
| `w` | `14250943/409241045000000` |
| `x` | `10541427/163696418000000` |
| `y` | `10578023/818482090000000` |
| `z` | `73741141/818482090000000` |

Every residual is nonnegative, so `Φζ(a)≤a`.  Notice also that

\[
  g=\frac{9499305}{10000000}=\frac{1899861}{2000000}<1.
\]

By the weighted-prefix lemma, for every positive `n`,

\[
  G(n)\zeta^n\leq\mathcal G_n\leq g<1.
\]

Using `A(n)≤G(n)` and `ζ>0`,

\[
  A(n)\leq \zeta^{-n}=\left(\frac{9047}{2000}\right)^n.
\]

Taking positive-index nth roots and then their supremum proves

\[
  \boxed{\lambda\leq\frac{9047}{2000}=4.5235}.
\]

## 5. Reproducibility and formal status

The arithmetic certificate has three independent exact replays:

1. Lean's ordinary kernel checks seventeen separately named `norm_num`
   theorems and their conjunction.
2. `Support/verify_certificate.py` uses only `fractions.Fraction`.
3. `Support/verify_certificate.wl` uses Wolfram Language exact rationals.

Candidate discovery is intentionally outside the trust boundary.  It used
fixed-point iteration near `ζ=2000/9047`, followed by a small displacement in
a positive near-critical direction and rational rounding.  Only the displayed
fractions and exact inequalities matter to the proof.

The Lean artifact separates a reusable conditional engine from its concrete
geometric instantiation.  `Main.lean` is intentionally abstract: it derives
the `9047/2000` supremal bound from either `WeightedBuiRecurrences` or
`BuiCoefficientRecurrences`, together with domination by the `G` coordinate.
`PublishedSystem.lean` provides the literal paper-facing
`PublishedBuiRecurrences` adapter and its pointwise and supremal endpoints.
These APIs make the algebraic content reusable and keep every hypothesis
visible.

The concrete path closes those hypotheses as follows.

1. `Polyomino.lean`, `Patterns.lean`, `Counting.lean`, and
   `GeometricProfile.lean` define the actual finite types and all seventeen
   marked-occurrence sequences, prove their degree-one values, and prove
   `A(n)≤G(n)` from the southwest type-`G` anchor.
2. `GeometricLinear.lean` and `GeometricDeletion.lean` prove the eight
   same-size or single-leaf rows.  `SeededPartition.lean` provides the common
   connected-territory lemma.  The split `P`, `Q`, `S`, `U`, `V`, and `W`
   core/geometry/endpoint chains, together with
   `GeometricTwoDeletion.lean`, give explicit finite injections for
   `P,Q,S,U,V,W,X,Y,Z`; `GeometricPPartition.lean`, `GeometricQ.lean`, and
   `GeometricVW.lean` are compatibility import surfaces for the corresponding
   split implementations.  `GeometricComplete.lean` assembles these facts
   into `geometricPublishedBuiRecurrences` for the actual profile.
3. The exact certificate and finite weighted-prefix theorem then give the
   closed pointwise estimate

   \[
     A(n)\leq(9047/2000)^n
   \]

   and the closed theorem
   `growthSup fixedPolyominoCount ≤ 9047/2000`.  These endpoint theorem
   statements have no recurrence, geometric-decomposition, or domination
   parameters; those obligations have already been supplied by the preceding
   modules.  Thus `Main.lean` remains the reusable conditional interface,
   while `GeometricComplete.lean` is its unconditional application to fixed
   polyominoes.

The relationship with the conventional definition of Klarner's constant is
formal as well.  `TranslationClasses.lean` constructs translation equivalence
as a quotient, proves that southwest normalization gives a canonical
equivalence between the quotient and normalized polyominoes, and identifies
`fixedPolyominoCount n` with the number of translation classes.
`Concatenation.lean` constructs an injective vertical stacking map

\[
  \mathcal P_l\times\mathcal P_m\hookrightarrow\mathcal P_{l+m},
\]

so the count is supermultiplicative; it also proves positivity at every
positive index.  `Asymptotic.lean` applies Fekete's lemma to the subadditive
negative logarithms, identifies the resulting limit with `growthSup`, and
proves

\[
  A(n)^{1/n}\longrightarrow\operatorname{growthSup}(A).
\]

Consequently the supremal bound above is the claimed bound on the usual
nth-root limit, not merely a bound on an auxiliary definition.

The development uses no project axioms, `sorry`, `unsafe` definitions, or
`native_decide` certificate boundary.  Its assumption audit is confined to
Lean/mathlib's standard logical axioms such as `propext`,
`Classical.choice`, and `Quot.sound`.  The human provenance boundary is the
transcription of Bui's seventeen diagrams into the finite coordinate tables
in `Patterns.lean`: those tables were manually audited against Bui v2,
page 15, but the Lean kernel does not visually read the PDF.  Given those
tables, the geometric recurrences, quotient/counting correspondence,
stacking supermultiplicativity, Fekete limit, and numerical endpoint are all
expressed as formal proofs rather than external assumptions.

## 6. References

- Vuong Bui, [*A convolutional approach to bounding the number of
  polyominoes*](https://arxiv.org/html/2511.00461v2), arXiv:2511.00461v2,
  6 May 2026.  See Theorem 2, Lemma 4, and Appendix B.
- Gill Barequet and Mira Shalah, [*Improved upper bounds on the growth
  constants of polyominoes and
  polycubes*](https://doi.org/10.1007/s00453-022-00948-6), Algorithmica 84
  (2022), 3559–3586.
