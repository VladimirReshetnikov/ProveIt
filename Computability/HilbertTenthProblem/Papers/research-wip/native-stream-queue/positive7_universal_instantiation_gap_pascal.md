# The missing finite data in the positive7 universal alphabet

This is a bounded text and source-interface audit. The inspected positive7
route proves existential universality and supplies an effective fixed-data
recipe. It does **not** yet supply a literal universal finite presentation,
its named embedding words, or a numerical universal relator count. The
missing work is earlier than matrix arithmetic: constructing one finite
Higman-operation description for the specific recursive presentation below.
The repository already identifies this gap in
`group_projective_general_separate_range.md`, Section 5. This note narrows
the first deliverable and distinguishes existing literal alternatives.

No scientific or supplied program, archived source, matrix list or arithmetic
source array was executed, imported or evaluated. No coefficients or degrees
were computed. The accompanying JSON records byte identities and exact
declared repository read spans. Search hits outside those spans are not
whole-file reviews. The external embedding proof remains an imported
foundation, not a newly certified 62-page proof.

## 1. The exact fixed data required by the current route

The commutator note fixes an effective enumeration of positive c.e. sets
S_p and the single set

    U={2^p(2x+1): p>=0 and x in S_p}.

It proves, with [g,h]=g h g^-1 h^-1, that

    G_U=<a,b | r_n=1 for n in U>,
    r_n=[b^-n a b^n,a],
    r_n=1 in G_U iff n in U, for n>0.                     (1)

An injective effective finite-presentation embedding must output a
two-generator presentation H0=<y1,y2 | R0> and literal words A0,B0
representing a,b. Adjoin fresh presentation letters a,b with the two
relations a=A0 and b=B0. The resulting four-generator presentation H
therefore has, with every listed relation retained,

    r=|R0|+2.                                             (2)

The named letters are free basis letters of the ambient free group F4;
they are not a faithful matrix representation of the quotient H. The
conjugated fibre product uses four paired generators
(a z_i a^-1,z_i) and r relator generators (1,R_j), together with their
inverses. Its raw labelled alphabet consequently has 8+2r slots.
Duplicate or identity letters may be retained. No numerical value of r
follows just from finiteness.

The subsequent free-group representation is already literal:

    U0=[1,1;0,1], V0=[1,0;4,1],
    a -> U0, b -> V0^3,
    y1 -> V0 U0 V0^-1, y2 -> V0^2 U0 V0^-2.

The projective6 and positive7 notes preserve the ordinary-input contract.
Program p determines alpha=12*2^(p+1) and gamma=12*2^p+1; x remains the
ordinary varying positive integer. The positive lift and the later local
coefficient recipes are finite fixed computations **after** R0,A0,B0 are
known. Their numerical coefficients, guard constants and universal r are
not supplied by the small r=1,2,4 arithmetic fixtures.

## 2. A concrete exponent-coding target

There is no need to leave the first source object as an unspecified word
language. Expanding (1) gives exactly

    r_n=b^-n a b^n a b^-n a^-1 b^n a^-1.

Define the normalized word map as the ordered product
W_f(a,b)=...a^{f(0)}b^{f(1)}a^{f(2)}b^{f(3)}..., with a at even
indices and b at odd indices. Set the following entries at indices
0 through 9, and set f_n(i)=0 at every other integer index:

    f_n=(0,-n,1,n,1,-n,-1,n,-1,0).                         (3)

Then W_f_n(a,b)=r_n exactly. The leading and trailing zeros supply a^0
and b^0. Define X_U={f_n:n in U}. This uses the alternating convention
of the paper's equation (4.8). If the displayed map in its Section 7.1
is used literally, take its variables x=b,y=a; see Remark 3. The two
generator-image words must follow that same fixed permutation.

Theorem B embeds the two-generator group encoded by X once its benign
pair K_X,L_X is supplied. With this explicit naming convention our
already two-generator input can enter there directly. The missing
**finite Higman-operation expression for X_U**
must retain n in U: the ten-entry pattern alone does not solve that index
restriction. Section 4.3 describes a general recursion route and conditional
shortcuts. [Mikaelian v8, Algorithm 1.1, Sections 4.2--4.4 and Theorem B](https://arxiv.org/pdf/2507.04347v8).

## 3. The conditional relator-count formula

Use the source's named-F3 normalization of K_X, including its three
distinguished free generators. Let K_X have m_H generators and n_H
relations, and L_X have k_H generators. These are not the positive7
alphabet size or program index.

The source's final extension has the ledger

    n_H+4m_H+k_H+78+7+2(1+m_H+20)+4
      =n_H+6m_H+k_H+131                                  (4)

relations. Its two-generator substitution retains these slots. Adding
our two naming relations gives

    r=n_H+6m_H+k_H+133.                                   (5)

This unpruned count has three unmaterialized inputs. It is neither a
minimum nor a numerical universal bound. The audit checks its composition
with (2), not all supporting HNN constructions.
[Mikaelian v8, Sections 7.8--7.9, equation (7.19) and Corollary 7.2](https://arxiv.org/pdf/2507.04347v8).

**Remark 3 (a printed parity mismatch, caught by root's challenge).**
Section 2.2 puts tuple entries at indices 0,1,... . Section 7.1 displays
odd-index x and even-index y, but its next example and equation (4.8)'s
exponent coding start with x at index 0; Section 7.2 likewise starts
with its first generator at index 0. For f=(1,0), the literal Section
7.1 display gives y, while the even-first convention gives x, distinct
free words. Our draft did not account for that mismatch when connecting
the tuple to Theorem B. The normalized map above fixes the indices;
the literal odd-first map is reconciled by x=b,y=a. This is a fixed
generator relabelling, with the embedding images relabelled as well,
not a claim that the two words coincide. It changes no relation-slot
count and does not refute the embedding theorem. The primary PDF's
printed pages 7 and 50 were inspected directly; page 50 was also viewed
as a rendered image. [Mikaelian v8, Sections 2.2, 4.2 and 7.1--7.2](https://arxiv.org/pdf/2507.04347v8).

**Remark 4 (root's conditional recipe-size observation).** The named-F3
normalization lists three distinct free generators, so m_H>=3. Since
n_H,k_H>=0, (5) gives r>=151 for this particular unpruned recipe. Thus
its actual numerical output would lie in the r>=8 collected-center
branch of the current local common-center theorem, not its r=1,2,4
fixtures. This is not a minimum over other embeddings or presentation
simplifications, and supplies no lower bound for arbitrary universal
group presentations or arithmetic circuits.

## 4. What the other literal repository candidates do supply

The report `group-theoretic-substrates/08-matrix-semigroup-core-README.md`
and its PROOF opening document 229 literal SL4(Z) generators, 93 directed
U15 rewrite rules and 114 tiles. They provide a finite-tape target encoder
for nonempty positive-semigroup membership. They explicitly do not adjoin
inverse generators, instantiate Higman, or provide the ordinary-affine
group input contract. The data files are named in the receipt as locations
only; their matrix entries were not evaluated or independently audited.
Their 229 cannot be used as our r or as the 8+2r subgroup alphabet without
an additional representation/interface proof.

`neary_woods_explicit_universal_tm.md`, lines 1--145, supplies the literal
U15 transition table and a proved ordinary-input tape construction using
the cited simulation. It is a concrete machine starting point, rather
than an unknown universal device. It still does not give R0,A0,B0 or an
enumerator-to-Higman-operation translation. Fixing a machine table alone
also does not specify our p-to-S_p enumeration and its encoding conventions.

The rational-rotation/dense-rational article's finite-presentation sections
explicitly invoke Higman existence and choose finite image words; they
state that those constants are not printed and that the code does not
implement Higman. The van Kampen source audit likewise says no Boone
relator table is instantiated. The affine-input audit imports the same
embedding interface. These inspected reports do not fill the gap.

**Remark 1 (the nine-rule shortcut fails in groups).** The existing
`tseytin_group_completion_obstruction.md` proves that C2's relations
force every letter to be the identity in every group interpretation:
cancel in cdca=cdcae to get e=1, then eca=ce and edb=de give a=b=1,
and caaa=aaa, daaa=aaa give c=d=1. Yet b is an isolated rewrite word,
distinct from aaa. Thus the literal universal nine-rule word table
cannot be substituted as an invertible-matrix group presentation
preserving its accepted language. Its separately paid rewrite substrate
and presentation-to-word reduction remain valid, distinct constructions.

**Remark 2 (existence and fixture counts).** No inspected source asserts
that a small r fixture is this universal group. Treating r=1,2,4, or the
semigroup count 229, as a materialized universal r is unsupported. We have
not proved that those values are impossible by every different group
construction. Mere undecidability of some other group's word problem
also does not supply (1), its two named images, or the ordinary-input map.

## 5. The smallest supported next instantiation task

Produce a finite, reviewable **X_U construction certificate**: fix one
explicit recognizer/enumerator and the program-index convention S_p;
specify the effective dovetailing and coding into U; and give a finite
Higman-operation expression whose resulting set is exactly (3). This
requires a proof of that expression's denotation. Merely enumerating more
accepted indices or printing the ten-entry tuple is insufficient.

The next dependent deliverable is the literal benign pair K_X,L_X, then
the finite two-generator R0 and the two embedding words A0,B0 obtained
from the cited constructions. Keep the substitutions and named-image
certificate with the output. Only then expand the four-letter fibre
product and compute its integer matrices and positive7 fixed numerals.
Correct specialization of these inherited embedding and substrate
theorems requires no new abstract universality theorem; it does require
the concrete construction and its interface proof. No existing inspected
alternative table bypasses those obligations for the present positive7
recipe.

**Question 1 (root's requested numerical instantiation).** Can the
specific ten-coordinate sequence pattern permit a manageable finite
Higman-operation expression for an explicit universal U? The general
effective theorem supplies a route, but no short expression or small
output bound has been proved here.

**Question 2 (alternative literal alphabets).** Can the documented U15
semigroup or another materialized machine be converted to this exact
named-commutator contract with fewer fixed data than the direct Higman
route? Their existing universality proofs establish different interfaces.
A new conversion proof and all ordinary-input costs remain outstanding.

## 6. Read and review scope

**Remark 5 (execution-scope correction).** The draft's opening phrase
"No program ... executed" was too broad. Fresh byte-metadata commands
and standard PDF text/rendering tools did run. No supplied or scientific
program, helper or saved arithmetic array was run or evaluated.

This note records a bounded dependency audit and the hand-checked
identities (2)--(5), not a universal finite-presentation construction,
matrix-table audit, or new complete operation bound. The repository
snapshot and byte/read-span bindings are in the JSON. The primary PDF
was read through versioned web text, then downloaded for ordinary text
extraction of pages 7 and 50 and visual inspection of page 50. Its bytes
are pinned as a reading cache; no full proof review is claimed. No new
scientific execution or repository mutation occurred.

Root fully challenged the draft, identified the retained parity issue,
then passed the corrected word convention, named images, count and
recipe-only floor; root also visually confirmed the printed mismatch.
Aristotle independently read the full revised 226-line mathematical draft,
checked the tuple and fixed swap against primary pages 7 and 50, checked
the count in pages 58--60, and passed every stated interface and scope
without further correction. These are bounded proof/interface challenges,
not full certification of the external embedding theorem. Final changes
only record that review provenance. This proof/metadata pair is frozen.
