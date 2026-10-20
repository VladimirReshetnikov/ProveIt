# A single HC countermodel blocks five restricted Łukasiewicz schemes, even with K

## The claim

Write the original propositional row as

\[
L(A,B,C,U)=((C\to U)\to A)\to((A\to C)\to(B\to C)).
\]

Replace its unrestricted fourth parameter by any or all of
`U=F`, `U=truth`, `U=A`, `U=B`, and `U=C`. Keep every other K220 native row,
the full seed-K bundle including support, modus ponens, generalization, and
truth code 0. In addition, allow all three schemes

\[
A\to A,\qquad F\to A,\qquad A\to(B\to A).
\]

**ZFC proves that this enlarged restricted calculus is consistent.**
Consequently, if ZFC is consistent, this modification cannot have the
requested ZFC-provable consistency equivalence with ZFC. This is an ordinary
mathematical proof, not a proof-assistant certificate. The accompanying
Python file independently checks the finite algebra used in the proof.

This strengthens `restricted_rho8_countermodel.md`: one matrix now handles
all five restrictions simultaneously and also validates the K combinator.
It does not justify removing an axiom from any different calculus.

## 1. The finite algebra

Use values `0,1,2,3`, with sole designated value `3` and falsum value `0`.
Implication has antecedent indexing the row:

| → | 0 | 1 | 2 | 3 |
|---|---:|---:|---:|---:|
| 0 | 3 | 3 | 3 | 3 |
| 1 | 3 | 3 | 1 | 3 |
| 2 | 3 | 3 | 3 | 3 |
| 3 | 0 | 0 | 0 | 3 |

The matrix validates every instance of the five restricted schemes, every
identity, ex-falso, and K. Modus ponens preserves designatedness. It fails
the unrestricted scheme at `(A,B,C,U)=(0,3,1,2)`, where the value is `0`.
It fails the S combinator at `(A,B,C)=(1,0,2)`.

Negation `N(v)=v→0` is Boolean: `N(3)=0` and `N(v)=3` for `v≠3`.
The native conjunction `N(A→N(B))` is Boolean and designated exactly when
both arguments are designated. For every Boolean consequent `b∈{0,3}`,

\[
(a\to b)=3\quad\Longleftrightarrow\quad a\ne3\ \text{or}\ b=3.
\]

Interpret a universal quantifier over a nonempty domain `D` as `3` exactly
when all instances are designated, and as `0` otherwise. Then the native
existential `N Q_i N A` is designated exactly when some instance is
designated. These facts follow directly from the table; they do not
presuppose propositional completeness.

## 2. HC and colored nonmembership

Work in ZFC and take `D=HC`, the set of hereditarily countable sets. Every
member of `HC` is a countable subset of `HC`, and every countable subset of
`HC` belongs to `HC`. Also `|HC|=2^{aleph_0}`: real codes for pointed
countable well-founded extensional relations give the upper bound, and
the reals themselves give the lower bound.

Choose an injection `f:HC→2^omega`. Replace it by the antichain encoding

\[
e(p)(2k)=f(p)(k),\qquad e(p)(2k+1)=1-f(p)(k).
\]

For every ordered pair `p≠u`, some coordinate has `e(p)=0,e(u)=1`.
Choose also `n:HC→omega` with every fiber uncountable; this exists because
`|HC|=2^{aleph_0}`. Equality takes value `3` for equal objects, `0` otherwise.
Interpret native membership by

\[
r(z,p)=
\begin{cases}
3,&z\in p,\\
0,&z=p,\\
1+e(p)(n(z)),&z\notin p\ \text{and}\ z\ne p.
\end{cases}
\]

Foundation makes these cases disjoint. Designated membership is actual
membership, and `r(z,z)=0`; therefore native falsum `F=R(0,0)` is always `0`.

The native subset formula

\[
\operatorname{Sub}(p,u)=\forall z\,(R(z,p)\to R(z,u))
\]

is designated **exactly when `p=u`**. If the objects agree, every implication
is an identity. If they differ, choose a coordinate `k` with
`e(p)(k)=0,e(u)(k)=1`. The fiber `n^{-1}(k)` is uncountable whereas
`p∪u∪{p,u}` is countable, so some `z` lies in the difference. Its membership
values are `r(z,p)=1,r(z,u)=2`, and `1→2=1` is not designated. The universal
subset formula therefore has value `0`.

## 3. The other logical rows

Interpret native code 0 as designated truth. Its exceptional alias
`I(0,0)=0` is sound because `3→3=3`. Every positive native code is evaluated
recursively by its strictly smaller formula fields; its relation/equality
fields are variable labels, as in the existing coding.

Generalization preserves truth under every assignment. For quantifier
distribution, designated `Q_i(A→B)` and `Q_i A` force every instance of `B`
to be designated by the matrix MP property. All quantified values are
Boolean, so the complete distribution formula is designated in the other
cases too. Quantifier commutation holds because both orders test the same
set of assignments, including when the labels coincide.

For rho6, `Ex_i Q_i A` has the same Boolean value as `Q_i A`. If that value
is `3`, the current instance of `A` is designated; if it is `0`, implication
to any value is designated. Equality existence follows by choosing the
object assigned to the other label. In the two membership substitution
rows, true equality makes the corresponding membership values literally
equal, so implication reflexivity applies; false equality has value `0`.

The G helper is valid because true equality premises force its equality
conclusion. The constructed binder is fresh from two distinct public
labels; with coincident labels the conclusion is reflexive under every
assignment. For gated atomic vacuity `R(a,b)→Q_cR(a,b)`, the gate ensures
`c≠a,b`. A designated atom remains designated under quantification. A
nondesignated constant atom is sent by the quantifier to `0`, and its
implication to `0` is designated. Thus every required non-K row is valid.

## 4. The entire native seed-K bundle

Fix the external parameters of a legal matrix code. The private container
label is the matrix code itself; the existing strict label bound makes it
fresh, with code 0 handled separately as truth. This is a coding fact
unchanged by the present semantics.

First suppose the two public labels are distinct. Let `Phi(y,p)` mean that
the matrix is designated under those assignments. This gives an arbitrary
relation on the set `HC`. The surrounding native conjunctions, existentials,
and implications with Boolean consequents show that the designatedness of
the seed-K part reduces exactly to

\[
\forall p\,\exists C\,[H(C)\land W(p,C)],
\]

where

\[
W(p,C):=(\exists y\,\Phi(y,p))\to
          \exists y\,(\Phi(y,p)\land y\in C),
\]

\[
H(C):=\forall u\in C\,
       [(\exists p\,\Phi(u,p))\land W(u,C)].
\]

Here native `Sub(p,u)` has become equality of objects, by Section 2. The
support conjunct `exists p Phi(u,p)` is retained in full.

Use Choice to select a witness function `g` on
`dom(g)={p∈HC: exists y∈HC Phi(y,p)}`. If the seed `p` is not in this domain,
take `C=emptyset`. Otherwise set

\[
C_0=\{g(p)\},\qquad
C_{m+1}=C_m\cup g[C_m\cap\operatorname{dom}(g)],\qquad
C=\bigcup_{m<\omega}C_m.
\]

The resulting `C` is countable, so it belongs to `HC`. Every element is some
selected witness `g(q)` and therefore has support. Whenever a member `u`
has a successor, its chosen successor `g(u)` belongs to `C`. Thus `H(C)`
and the seed condition `W(p,C)` both hold.

If the public labels coincide, the outer seed is shadowed and `W` becomes

\[
(\exists x\,\Phi(x))\to
\exists x\,(\Phi(x)\land x\in C).
\]

The subset test is reflexive. If there is no witness choose the empty
container; otherwise choose one witness `q` and `C={q}`. The shadowed
support and closure clauses then hold. This covers the coincident-label
instances, rather than assuming distinctness that the emitter does not
enforce.

The other bundle conjunct is gated membership vacuity, already checked.
If the gate finds equality between private and public labels, it emits
truth code 0. Therefore every emitted native bundle is designated.

## 5. Formalizable consistency conclusion and limits

HC, its two coloring functions, the assignment set `HC^omega`, and the
finite-valued recursive evaluator are all sets definable in ZFC. The matrix
calculations and the HC closure proof establish every axiom and rule.
Induction on the length of any finite native derivation makes every theorem
designated under every assignment. Native falsum always has value `0`, so
it is not derivable. This proves the stated consistency assertion in ZFC.

If ZFC additionally proved the proposed consistency equivalence, it would
prove its own consistency; under the usual consistency hypothesis this is
excluded by the second incompleteness theorem. The result is specific to
these five parameter restrictions with the listed extra schemes. It does
not exclude other three-parameter bases, other semantics, or the separate
rho6-to-T proposal.

Run `python3 research_calculus/restricted_rho8_strong_countermodel.py` for
the independent finite receipt. Its 320 restricted-schema checks and 4,368
distribution-vector checks are evidence only for the finite algebra; the
unbounded HC argument is the mathematical proof above.
