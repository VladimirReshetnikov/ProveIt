# A two-relator affine-line transducer for a benign pair

This separate handwritten lemma maps a benign pair whose elements encode a
single integer parameter directly to any fixed nonconstant affine line of
tuples. It adds one presentation generator and two relators. Applied to the
accepted configuration relation, it avoids both unary extraction and the
subsequent pattern-cylinder construction. These are declared presentation
counts; no complete presentation or matrix alphabet is materialized here.

Aristotle proposed this extension after the shared-ambient note froze. The
source action lemma and ambient embedding premises remain those of that
note. The new free-pair and intersection arguments below are direct normal-
form arguments. Root, Pascal and Riemann independently passed the full
written draft; the proof and its byte/read-scope receipt are now frozen.

## 1. State and a free affine-orbit pair

Let K be a finitely presented group containing the distinguished free group
F=<a,b,c> and the tracked embedded copy of the fixed nine-generator group A
from the shared-ambient construction. The tracked A has the same marker
triple. Write conjugation as x^y=y^-1 x y, and retain

    b_i=c^-i b c^i,  b_f=product_[i increasing] b_i^f(i),
    a_f=a^b_f,  d_i=e^-i d e^i.

For fixed finitely supported integer vectors f0 and v with v nonzero, set

    a0=a_f0,  w=product_[i increasing] d_i^v(i).

The imported signed translation action gives

    a0^(w^n)=a_(f0+n v) for every integer n.             (1)

The pair (a0,w) freely generates a rank-two subgroup of A and hence K.
Here are all the needed normal-form details. In the free group <b,c>, the
conjugates b_i freely generate the kernel of the map c->1,b->0 to Z.
Consequently the sorted words b_f are distinct for distinct vectors f. In
F=<a>*<b,c>, the kernel of the retraction killing a has free basis
{a^u:u in <b,c>}. Thus the distinct elements a_(f0+n v) form a free family.
Likewise the words d_i freely generate a subgroup of the embedded free
group <d,e>, so w is nontrivial and has infinite order.

Map the abstract free group <x,y> to <a0,w> by x->a0,y->w. Collect a reduced
word into a word in the free basis {x^(y^n):n in Z} of the exponent-y kernel,
followed by y^k. If k is nonzero, its image has nontrivial retraction w^k
under A->Free(d,e). If k=0 and the original word was nontrivial, its image
is a nontrivial reduced word in the distinct free family from (1). This
proves injectivity. Only the retraction of the embedded A is used, not a
retraction of all K.

## 2. Exact transduction with one HNN letter

Suppose (alpha,beta) freely generates a rank-two subgroup G of F, and a
stored finite list L in K has

    F intersect <L> = <alpha^(beta^n):n in U> = H.      (2)

Here U is any subset of Z; no enumeration or decision about its membership
is used. In particular H is contained in G. By Section 1 the assignment
alpha->a0,beta->w is an isomorphism psi:G-><a0,w>. Form the explicit HNN
extension

    Q=<K,t | alpha^t=a0, beta^t=w>.                    (3)

It embeds K. The returned subgroup list is L^t, conjugating every listed
word by this single new letter. Its length is unchanged. Britton's lemma
gives the exact identity

    K intersect <L^t> = (<L> intersect G)^t.            (4)

Indeed every element of <L^t> is t^-1 h t with h in <L>; it can be an
element of K exactly when h lies in the associated input subgroup G.
Since G is contained in F, (2) gives <L> intersect G=H. Formula (1) shows
that H^t is A_(f0+U v), already contained in the old marker F. Therefore

    F intersect <L^t> = A_(f0+U v).                    (5)

This proof does not claim that t normalizes F: generally it does not,
because w need not lie in F. Equation (4), rather than an unjustified
conjugation of the whole F-intersection, is the required boundary argument.
All old cached intersections and the tracked A remain valid because K
embeds in Q. The exact update is (g,r,l)->(g+1,r+2,l).

## 3. The accepted-configuration and pattern instance

Pascal's frozen affine recognizer has Accepted supported at sites 0,1,
with the exact tuples (23,n,0,...), n in the fixed universal unary set U.
Its stored list satisfies (2) with

    alpha=a^(b^23), beta=b^c,
    alpha^(beta^n)=a^(b^23 (b^c)^n)=a_(23,n).

The pair is free: the substitution a->a^(b^23), b->b^c, c->c is a free-
group automorphism, the composition of partial conjugation of a by b^23
after the automorphism fixing a,c and sending b to b^c. No existing d_i
or shift word is assumed to implement this whole substitution.

Use the pattern's fixed vectors

    f0=(0,0,1,0,1,0,-1,0,-1,0),
    v =(0,-1,0,1,0,-1,0,1,0,0).

Their target words are explicit:

    a0=a^(b_2 b_4 b_6^-1 b_8^-1),
    w=d_1^-1 d_3 d_5^-1 d_7.

Formula (5) returns precisely the X_U pattern subgroup. Conditional on
the separately counted Accepted state (498,17676,3), the result is

    X_U: (499,17678,3).

The inherited subsequent presentation-count formula r+6g+l+133 then
evaluates by hand to 20808. This is a conditional schedule number, not a
materialized universal presentation, established matrix count, arithmetic
gate bound, or a re-audit of the inherited final embedding theorem.

## 4. Retained boundaries

**Remark 1 (do not use unrestricted intersection transport).** It would
be incorrect to justify (5) by asserting F^t=F. The new target generator
w has nontrivial image in Free(d,e), whereas every element of F has
trivial image. Britton's exact K-intersection (4) is the repair.

**Remark 2 (the nonconstant direction is needed).** For v=0 the displayed
w is identity; the target pair cannot be a rank-two HNN associated group.
The constant-image case is not part of this uniform recipe. The actual
pattern has nonzero v, so this boundary does not change the application.

**Remark 3 (earlier routes remain valid).** The generic theta projection,
the one-generator/three-relator full-F automorphism decoder, and the
Keep/cylinder construction remain valid less economical schedules. Their
already recorded counts and any retained prior arithmetic corrections are
not rewritten by this separate lemma.

Evidence is handwritten mathematics and inert reading only. No supplied or
frozen program, presentation expander, arithmetic source array, scientific
calculation, symbolic propagation, or build was executed. Fresh byte/read-
span metadata authenticates the immutable parent notes. Root, Pascal and
Riemann each checked the full free-pair argument, exact Britton orientation,
explicit words, preserved marker/cache and conditional counts; no correction
was requested. Their challenges do not certify a materialized presentation
or expand the imported primary-source theorem scope.
