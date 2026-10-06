# A finite two-generator embedding with every named word specified

For any finite presentation G=<g_1,...,g_m | R>, m>=1, the full universal
words below give an injective embedding into a two-generator presentation
with exactly |R| declared relator slots. The proof uses only finite HNN
extensions, one amalgam and explicit Tietze eliminations. It works with
torsion and with generators that represent the identity. It does not use
the defective Section 7.4 construction of arXiv:2507.04347v8.

This is the finite-m specialization of V. H. Mikaelian, *Embeddings using
universal words in the free group of rank 2*, arXiv:2002.09433v4, Theorem
1.1 and Sections 3.1--3.2. Root supplied the concrete finite proof route
and the counterexample to an unqualified shortened formula; Aristotle
independently checked the complete construction below. The read scope is
LF1--340 of the ordinary extraction, with visual page5 for Section3.3.
No countably infinite construction, literature comparison or matrix
materialization is claimed by this note. Root and Riemann independently
passed the full written proof; this note and its byte/read-scope receipt
are frozen after their challenges.

## 1. The exact full words and conclusion

All conjugation is right conjugation u^v=v^-1*u*v. For i=1,...,m define
the literal words on two fresh names x,y by

    q_i=(x*y^i)^2*x^-1,
    w_i=y^q_i * (y^-1)^x
       =x*(y^-i*x^-1)^2*y*(x*y^i)^2*x^-2*y^-1*x.       (1)

In particular the primary shorthand y^(-x) means (y^-1)^x, not y^(x^-1).
For each inherited relator r in R, let r(w_1,...,w_m) denote the literal
substitution g_i->w_i and g_i^-1->w_i^-1. Put

    T_G=<x,y | r(w_1,...,w_m), r in R>.                (2)

Then g_i->w_i defines an injective homomorphism G->T_G. The relator list
keeps the original order and all slots, including redundant or trivial
ones; its declared length is exactly |R|. No minimum-relator claim or
automatic simplification is used. Formula (1) is uniform in the supplied
presentation and requires no decision about which g_i are nontrivial.

## 2. First finite HNN stage

Choose a fresh auxiliary a_* and form B=G*<a_*>. The homomorphism B->Z
that kills G and sends a_* to1 shows that each g_i*a_* has infinite order,
even when g_i is torsion or identity. Both <a_*> and <g_i*a_*> are
infinite cyclic, so their generator assignment is an isomorphism. Define

    P=<G,a_*,t_1,...,t_m | a_*^t_i=g_i*a_*, 1<=i<=m>.
                                                               (3)

The multiple-HNN normal-form theorem embeds B, hence G, in P. The t_i
freely generate a free rank-m subgroup U: killing B defines a retraction
P->Free(t_1,...,t_m), which splits the inclusion of their free group.
Also <a_*> intersect U is trivial. Indeed the retraction kills every
a_* power and is injective on U; the surviving a_* remains infinite in
the embedded B. No assumption that G is torsion-free was made.

## 3. The auxiliary free family and the finite amalgam

In Y=Free(y,z), put s_i=y^i*z^i for 1<=i<=m. These are a free basis
of their generated subgroup V of rank m, not merely m distinct words.
For a direct proof set v=y*z and v_j=y^j*v*y^-j. The pair (y,v) is a
free basis of Y, and the v_j, j in Z, freely generate the exponent-y
kernel. For positive i,

    s_i=v_(i-1)*v_(i-2)*...*v_0;
    v_0=s_1, v_j=s_(j+1)*s_j^-1 for 1<=j<m.           (4)

These substitutions are inverse triangular free-basis changes: substituting
the second into the first telescopes to s_i. Thus s_1,...,s_m are free.
The homomorphism Y->Z given by y->1,z->-1 kills every s_i, so

    <y> intersect V = {1}.                            (5)

Amalgamate P and Y by t_i=s_i. This is an isomorphism U->V by the two
free-basis proofs, so both factors embed in

    C=P *_(U=V) Y.

The cyclic subgroups <a_*> in P and <y> in Y have trivial intersections
with the amalgamated subgroups. An alternating nonempty reduced word in
their nontrivial powers remains reduced in the amalgam. Consequently
<a_*,y>=<a_*>*<y> is a free group of rank two in C. The entire Y is
also still an embedded free group of rank two.

## 4. Final HNN stage and exact elimination

The assignment (y,z)->(a_*,y) is an isomorphism between these two free
rank-two subgroups. Append one fresh x to form

    H=<C,x | y^x=a_*, z^x=y>.                         (6)

Again the base embeds, so G embeds in H through all stages. A finite
presentation of H has 2m+4 names and |R|+2m+2 relators: the original
R, m relations in (3), m amalgamation relations and two relations in (6).
Every subsequent elimination is now explicit:

    a_*=y^x;
    z=y^(x^-1)=x*y*x^-1;
    t_i=y^i*z^i=y^i*x*y^i*x^-1;
    g_i=a_*^t_i*a_*^-1
       =y^(x*t_i)*(y^-1)^x=w_i.                      (7)

Here x*t_i=(x*y^i)^2*x^-1, which is exactly q_i in (1). Use the two
relations of (6), the m amalgamation relations, and the m relations of
(3) as definitions to eliminate a_*,z,t_i,g_i respectively. They remove
2m+2 names and exactly 2m+2 defining relators. The remaining presentation
has just x,y and the original |R| relators with substitution (1): it is
(2). Tietze transformations preserve the constructed group, including
the proved embedding and the specified images of each g_i. This proves
the conclusion directly for finite m, without an unproved normal-closure
intersection assertion or an infinite presentation expansion.

## 5. Application to the separate centralizer branch

The frozen centralizer lemma supplies a finite presented group Q with
the named word family

    W_n=[alpha^(beta^n),t],
    alpha=a^(b^23), beta=b^c,
    W_n=1 in Q iff n belongs to U.

Enumerate its declared generators as g_1,...,g_m in the supplied order
and apply (1) to all of them, including its centralizer letter. Let
A,B,T be the respective substituted words for alpha,beta,t. Injectivity
gives the exact same-parameter equivalence

    [A^(B^n),T]=1 in T_Q iff n belongs to U.           (8)

Thus the two-generator word interface is explicit as a finite substitution.
For the hand-counted m=499, |R|=17679 centralizer branch, it gives a
two-generator presentation with 17679 declared relator slots. This count
does not materialize or independently audit those substituted relators.
The ordinary-input n is unchanged; the program/input coding is exactly
the one in the frozen centralizer note.

The existing positive7 loader still has its particular matrix and
commutator input form. The three fixed words A,B,T in (8) are not thereby
its designated generators, and the parameter appears in B^n. This note
does not provide the needed paid arithmetic loader, matrix alphabet or
complete history certificate for that interface. It gives no numerical
universal arithmetic improvement.

## 6. A precise failure of the shorter formula

**Remark 1 (identity-valued named generators).** Primary Section3.3 and
Theorem3.2 propose the shorter words bar_w_i=y^q_i for a torsion-free
presented group. The displayed theorem and preceding presentation
conventions do not require every named generator to be nonidentity.
Under that unqualified reading take

    G=<g_1,g_2 | g_1=1>, which is infinite cyclic.

It is torsion-free. In the shortened target, its sole substituted relation
is bar_w_1=1. A conjugate of y being identity forces y=1, so bar_w_2=1
also. The nontrivial g_2 is killed. Hence that named-generator map is not
injective for this permitted presentation. This is a counterexample to the
unqualified presentation formulation, not to Theorem1.1's full words or
to a shorter construction with an extra infinite-order hypothesis on
every supplied generator. The missing issue is that the identity has
order one even in a torsion-free group.

The full construction (3) avoids this boundary because g_i*a_* always
has exponent-a_* equal to1. No deletion of identity generators, and no
decision about which they are, is assumed. The terminal (y^-1)^x factor
in (1) is retained in every substitution, including all inverse words.

**Question 1 (paid arithmetic interface, credited to root).** Materialize
and authenticate the actual finite substitution with its named query
ports, then supply a faithful matrix/arithmetic realization of (8) with
every input, selection and history cost paid. A finite two-generator
embedding is now proved; the required arithmetic interface does not
follow from the generator or relator-slot count alone.

Evidence is hand group theory and inert primary/parent reading. No
presentation expander, group-word evaluator, saved source array, frozen
helper, scientific computation, symbolic propagation or build was run.
Ordinary PDF rendering and fresh byte/read-span metadata are the only
machine preparation beyond text reads. Root independently read the full
178-line mathematical draft and passed every stage, elimination, word and
scope boundary. Riemann separately passed that complete proof and read
primary LF30--75,110--140,200--214,235--282 to confirm the exact scope of
Remark1; he did not claim a full primary-paper or visual audit. Neither
review requested a correction. Final edits change only this provenance
and status, with all mathematical words and counts retained.
