# A linear projective input and a three-operation mortality loader

The universal group construction admits an exact **affine vector input**
with two arithmetic operations. Its six-dimensional symmetric-square
lift has a **three-operation positive input column**, and the same three
operations load its entire rank-one mortality generator. This improves
the endpoint interface of the
[seven-dimensional Gram construction](group_gram_zero_mortality.md).

The key is a property of the specific conjugated fibre-product subgroup.
Its projective ambiguity can be eliminated inside the original graph
group, so a full matrix-equality test is unnecessary. The theorem uses
one fixed alphabet for all programs and the ordinary positive input x.
It has no word-height hypothesis.

This packet does not encode an arbitrary selected matrix word. A paid
positive certificate for each **fixed** physical word is given in
Section 6; its size still grows with that word. The universal finite
presentation and its numerical matrix alphabet are inherited abstractly,
not transcribed here. The [source](group_projective_zero_mortality6.py)
and [receipt](group_projective_zero_mortality6.json) check the algebra
and these boundaries using exact integer arithmetic.

## 1. The inherited group interface

Use the [established group construction](group_commutator_universal_substrate.md).
For an r.e. set S of positive integers let

    G_S=<a,b | [b^(-n) a b^n,a]=1 for n∈S>,
    a_n=b^(-n) a b^n.

It proves `[a_y,a]=1 iff y∈S` for y>0. It also realizes G_S as a
semidirect product of the graph group on vertices c_i, i∈Z, with
commutation edges |i−j|∈S and the shift action, identifying a_i with c_i.
In particular there are the following two homomorphisms:

* On G_S, the b-exponent sends b to 1 and every a_i to 0.
* On its graph-group kernel, c_i maps to the independent basis vector
  e_i in the direct sum of copies of Z indexed by Z.

The second map is well-defined because all graph relations are
commutators. It is not asserted to extend to the semidirect product.

The same established construction effectively embeds G_S in a finite
presentation H whose free presentation group F_4 has named basis letters
a,b and two other letters. Write π:F_4→H for the quotient. Define

    M(H)={(g,h)∈F_4×F_4 : π(g)=π(h)},
    M_a=(a,1) M(H) (a^(-1),1).

This is a finitely generated subgroup, with the explicit finite
generator recipe in the parent. Importantly, an equality involving
only the named elements of G_S can be pulled back from H to G_S by
injectivity of the embedding. No exponent homomorphism on H is assumed.

For one alphabet representing all r.e. sets S_p, use the fixed r.e. set

    U={2^p(2x+1) : p>=0 and x∈S_p}

and perform the construction once for G_U. The remaining steps use
this single H and single subgroup.

## 2. The exact rational-point stabilizer

Use precisely the swapped Schreier representation from the parent:

    U0=[1,1;0,1], V0=[1,0;4,1],
    a↦U0, b↦V0^3=[1,0;12,1],
    z1↦V0 U0 V0^(-1), z2↦V0^2 U0 V0^(-2).

Let Γ be the image of F_4. The parent proves the ambient group
<U0,V0> is free and this representation is faithful. Its image Γ is
exactly the kernel of the homomorphism

    <U0,V0>→Z/3, U0↦0, V0↦1.

For completeness, the transversal 1,V0,V0² rewrites every kernel word
as a word in U0,V0 U0 V0^(-1),V0² U0 V0^(-2),V0³ and their inverses.
Conversely all four displayed generators have V0-exponent zero modulo
three. This proves the kernel identity used here.

Every ambient word has diagonal entries 1 modulo four and lower-left
entry zero modulo four. These congruences form a subgroup condition,
so they hold also for inverses. If such an integral determinant-one
matrix is lower triangular, its diagonal entries must both be 1 or
both be −1. The congruence excludes −1. It is therefore V0^j for some
integer j. Faithfulness of the ambient free group makes its exponent
j, and membership in Γ forces j divisible by three. Hence

    Γ ∩ {lower-triangular matrices} = <ρ(b)>.       (1)

In particular every element in this intersection fixes e2=(0,1)^T
exactly, not merely projectively. Torsion-freeness alone would not
justify the positive diagonal sign in this argument; the congruences
are used explicitly.

For a positive integer y put r=12y and

    L=ρ(a_y)=[1+r,1;−r²,1−r],
    v=L^(-1)e2=(-1,r+1)^T.

For P∈Γ, the first coordinate of Pv vanishes if and only if P L^(-1)
is lower triangular. Equation (1) gives the exact equivalences

    (Pv)_1=0
      iff P=ρ(b)^n L for some n∈Z
      iff Pv=e2.                                 (2)

The analogous statements hold for the other block Q. Outside Γ the
last equivalence can fail: P=−L maps v to −e2 and still has first
coordinate zero. This packet never applies (2) to arbitrary SL2 words
without the fixed subgroup or its paid macro-language control.

## 3. The two projective ambiguities disappear

Let K be the faithful matrix image of M_a. For the preceding y,r,v,

    y∈S iff ∃(P,Q)∈K: (Pv)_1=(Qv)_1=0
         iff ∃(P,Q)∈K: Pv=Qv=e2.                 (3)

The forward implication takes P=Q=L, as in the established universal
group theorem. To prove the converse, equation (2) gives unique n,m∈Z
and free words P=b^n a_y,Q=b^m a_y. Membership in M_a means

    a^(-1) b^n a_y a = b^m a_y in H,

or equivalently

    a_y a a_y^(-1) = b^(-n) a b^m in H.          (4)

Every term in (4) belongs to the embedded original G_S. Pull the
equality back there first. Applying its b-exponent homomorphism gives
m=n. Thus (4) becomes

    c_y c_0 c_y^(-1) = c_n

in the graph-group kernel. Its abelianization map from Section 1 gives
e_0=e_n, so n=0 and therefore also m=0. The remaining equation is
`[a_y,a]=1`, which holds exactly when y∈S. This proves both directions
of (3) for arbitrary subgroup words, without bounding their entries
or lengths.

Both blocks are necessary for this proof. The subgroup M_a projects
onto each free factor. More explicitly, for any target L the pair
(L,a^(-1)L a) lies in M_a because its inverse conjugate is diagonal.
It always passes the first projective test. Thus using only that test
would accept every input, including inputs rejected by the two-block
predicate. This is an exact obstruction to that particular dimensional
simplification, not a general lower bound on matrix representations.

For the single universal K_U, precompute

    α=12·2^(p+1), β=12·2^p, γ=β+1.

The ordinary input is still x>0, with r=αx+β and t=r+1=αx+γ.
The vector v=(-1,t) needs just `α*x`, then addition of γ:
**2=1M+1A**. These are fixed program numerals. No run-time exponent or
input recoding witness is used. The affine-input obstruction for
SL2-matrix subgroup membership does not apply to this vector-action
predicate.

## 4. A six-dimensional scalar zero with positive quadratic input

Use the three-dimensional representation S(A) from the Gram packet,
with (a,b,c) standing for the symmetric matrix [a,−b;−b,c]. Explicitly,
for A=[p,q;s,d],

    S(A)=[p²,−2pq,q²; −ps,pd+qs,−qd; s²,−2sd,d²].

It satisfies S(AB)=S(A)S(B) and maps the coordinates of G to those of
A G A^T. The rank-one matrix vv^T has coordinates (1,t,t²). Set

    ρ6(P,Q)=diag(S(P),S(Q)),
    u6=(1,0,0,1,0,0),
    v6(x)=(1,t,t²,1,t,t²)^T.

Then, for any integral P,Q,

    u6 ρ6(P,Q) v6(x) = ((Pv)_1)²+((Qv)_1)².      (5)

This is nonnegative and vanishes exactly when both projective tests
hold. The finite signed generator alphabet of K_U maps to a fixed
alphabet of invertible integral 6×6 matrices. Combining (3) and (5)
proves an exact all-r.e.-sets scalar-zero contract over that one alphabet.
The input loader is

    scaled=α*x, t=scaled+γ, t2=t*t,

costing **3=2M+1A**, with degree-two output and no existential witnesses.
All six supplied-to-the-action input entries are positive. Their copies
and the fixed coordinate one cost no arithmetic. Arbitrary positive
α,β also define this arithmetic loader; the universal corollary uses
the compatible program constants above and the corresponding fixed K_U.

## 5. The same three gates load the whole mortality generator

Put R_x=v6(x)u6. It has exactly two nonzero columns, both equal to v6(x):

    row_i(R_x)=(v6_i,0,0,v6_i,0,0).

Its entries are copies of 1,t,t² and zero, so the full rank-one matrix
has the same **3=2M+1A** input cost. It is nonnegative, has rank one,
and satisfies R_x²=2R_x. Thus repeating the sentinel alone never
creates a spurious zero product, independently of x.

The [rank-one mortality lemma](group_gram_zero_mortality.md) applies
because every fixed letter ρ6(P,Q) is invertible. A product with
several R_x factors is zero precisely when one of the internal scalar
factors u6 A v6(x), A a possibly empty fixed-alphabet word, is zero.
Conversely u6 A v6(x)=0 gives R_x A R_x=0. Therefore

    x∈S_p iff the fixed six-dimensional alphabet together with R_x
                generates the zero matrix.                     (6)

The sentinel may repeat freely. There is no order restriction or
once-only boundary condition hidden in (6). Exactly one matrix varies
with x; the other matrices are fixed once for all programs. The size
of that finite alphabet is inherited from the uninstantiated group
presentation, not a new numerical alphabet bound.

The fixed alphabet necessarily still uses signed entries in this
construction. Were every matrix nonnegative, mortality would depend
only on their zero patterns. The zero pattern of R_x is constant for
all positive x, so a fixed nonnegative alphabet could recognize only
all inputs or none through this interface. This inherited support
obstruction is separate from the signed construction in (6).

## 6. Paying for a positive certificate of a fixed physical word

The rank-one Gram matrices here are positive semidefinite; their
diagonal entries can be zero. In fact an accepting endpoint is
(a,b,c)=(0,0,1). Thus the earlier positive-definite Gram packet's
unshifted positive diagonal witnesses cannot be reused unchanged.

For a fixed word of length ell in signed unit shears on the two
blocks, supply one common D>0 and use

    Ahat=a+1, Bhat=b+D, Chat=c+1.

Initially these are `2,t+D,t²+1` in each block. The paid common
registers t+D, t²+1 and 2D=D+D cost three additions. For a shear with
fixed sign ε, let Yhat be the changing diagonal and Zhat the unchanged
one. The two next positive supplied coordinates satisfy

    Bhat'=Bhat−ε Zhat+ε,
    Yhat'=Yhat−ε Bhat−ε Bhat'+2εD.                (7)

Direct signed additions/subtractions cost two and three gates,
respectively: **five additions per step**. Copy the unchanged state
coordinates. Finally compare

    Ahat_final+OtherAhat_final=2,

using one addition. The complete literal circuit costs

    3 loader + 3 shared shifts + 5ell steps + 1 endpoint
      =5ell+7 = 2M+(5ell+5)A.

There are 2ell+1 positive witnesses and 2ell+1 comparisons: one D and
two new coordinates per step, with one final endpoint comparison.
The literal sum of squared residuals costs

    11ell+9 = (2ell+3)M+(9ell+6)A.                (8)

For every nonempty word its exact total degree is four. All residuals
have degree at most two. At the first shear, the initial quadratic c
occurs with nonzero coefficient in the upper Bhat residual or the
lower diagonal residual, so one residual has degree two. Highest
squares cannot cancel. The empty word instead has constant residual
two and does not accept; the literal unused gates can still be emitted.

Soundness follows by decoding a=Ahat−1,b=Bhat−D,c=Chat−1 in (7).
The comparisons force exactly the Gram action. For completeness every
actual diagonal is nonnegative, so its hat is positive. A sufficiently
large common D makes the finitely many Bhat values positive too.
The endpoint is exactly (5). No hidden digit range or determinant
condition is required for this fixed-word result.

Only for a full word belonging to the prescribed fixed macro language
does Section 3 identify this endpoint with the universal group query.
The individual physical unit shears need not lie in Γ. Arbitrary word
selection, macro-language control and a uniform packed history are not
paid in (8). It is a family of fixed-word degree-four polynomials with
growing witness count, not a fixed universal degree-four polynomial.

## 7. Reproducible evidence and scope

The checker enumerates 4,373 ambient reduced free words to test the
mod-four and lower-stabilizer identities. It separately checks 512
projective cases, including prescribed nonzero stabilizer powers.
Another 1,452 signed exponent cases verify the exact semidirect
coordinates behind (4), rejecting unequal exponents by the shift map
and equal nonzero exponents by the graph abelianization. Twelve finite
relator examples construct actual fibre-product words, their matrix
images, scalar zeros and mortal sentinel products. They are finite
illustrations, not a transcribed universal finite presentation.

Arithmetic tests cover the three-gate loader, dense symmetric-square
products, repeated-sentinel factorizations, actual positive fixed-word
histories, independently expanded residuals on arbitrary positive
witness assignments, and exact degree-four slices. Accepting words,
changed ordinary inputs, zero diagonal endpoints, and the outside-Γ
negative-sign counterexample are included. The source imports only
the already reviewed Gram arithmetic and elementary free-word helpers.

Run it normally to compare the deterministic receipt; use
`--write-receipt` to regenerate it. No parent source or central
navigation file is changed by this packet.

An independent full proof/source/default review passed without findings.
It checked the exact Schreier kernel and congruence sign, both subgroup
ambiguity eliminations, the three-operation full sentinel, repeated
sentinel products, all positive fixed-word shifts and counts, and exact
degree four for nonempty words. An additional 512 independently formed
residual, sum-of-squares and dense-vector trajectory checks passed.
