# Word-level premises for the shared Higman schedule

This focused audit matches the normalized rho, pi and omega recipes to the
literal primary constructions and specifies their marker transport. The
normalized words and counts pass within the imported subgroup-identification
scope below. It does not execute or certify a presentation emitter, compare
expanded relator arrays, or re-prove all of the primary normal-form lemmas.
The independent literal-output comparator remains a separate task.

The source is Mikaelian, arXiv:2507.04347v8, Sections 5.3, 6.5, 6.8 and 6.11.
The fixed PDF, LF-delimited extraction and exact read spans are bound in the
receipt. The frozen normalized recipe, persistent-ambient and shared-schedule
notes are the local premises. Fresh auxiliary groups below are still paid:
the existence of a tracked initial A does not permit identifying them with it.

## 1. Literal word and naming conventions

Use right conjugation x^v=v^-1*x*v and hence (x^v)^w=x^(v*w).
For signed integer i, b_i=c^-i*b*c^i, d_i=e^-i*d*e^i, and
h_i=k^-i*h*k^i. The sorted product b_f uses increasing integer indices.
An instruction "t sends U_i to V_i" contributes exactly
t^-1*U_i*t*V_i^-1 for each listed pair. "t fixes W" is the same rule
with U_i=V_i. Unmentioned ambient generators receive no additional fixing
relations. A map on a named free subgroup is not silently a map on all K.

Every occurrence has a fresh private namespace. A displayed base-generator
list contains each declared name once after the explicitly prescribed
marker identification; equal words, maps or group elements do not justify
merging different declared letters. Inherited relators are retained once.
No commutation or cancellation of scientific words is assumed by this
specification. A renderer may use a different consistent ordering for a
finite generating list, but its literal comparator must fix that order.

A barred input means a bijective copy of the whole input presentation and
every stored word. It may be implemented by retaining the old numeric IDs
and treating them as the barred roles, rather than renumbering every word.
This is a naming isomorphism only: the new unbarred output marker and all
private auxiliary letters remain fresh. The same convention applies when
omega calls the old marker g0,h,k. The role map must be explicit.

## 2. Reflection rho and its extraction

In the fixed A, the nine names are a,b,c,t,t',u1,u2,d,e; all twenty
relations are those in the normalized note and primary (5.10). Append a
fresh barred auxiliary A to the barred input along its three marker names:

    Kbar0 = Kbar *_(Fbar) Abar;  P=Kbar0 x A.

The direct product contributes one commutator between each of the nine
unbarred A generators and each of the g+6 distinct Kbar0 generators. Thus
P has g+15 names and r+9g+94 relators. With separate fresh letters put

    v1 fixes (abar*a, dbar*d, ebar*e^-1);
    v2 fixes (Lbar, a,d,e);
    LQ=(X_Abar, X_A)^(v1*v2).

The list LQ has eighteen words. Its order may be fixed as barred nine then
unbarred nine. The source graph identification is imported from Section
6.5.1; the orientation is independently checked: the ebar coordinate maps
to e^-1, so dbar_i acts as d_-i. It does not invert d or the values f(i).
The example f=(2,5,3) becomes values 3,5,2 at sites -2,-1,0, respectively.

The resulting product of d_-i factors is in reversed index order. Primary
Remark 5.13 equates its action on a with the sorted reflection word; it
does not equate or commute the literal d_i words in A. This action premise,
and the primary graph-intersection lemma, are separate from string equality.

Use C6=(a,b,c,abar,bbar,cbar). The extraction is exactly

    w1 fixes (abar,bbar,cbar);
    w2 fixes LQ;
    w3 fixes (a,b,c);
    w4 fixes (C6^w1,C6^w2);
    Lrho=C6^(w3*w4).

This adds 3+18+3+12=36 relators, after the two v letters added l+6.
Before persistent transport the result is g+21,r+9g+l+136,list6.
The output marker is the fresh unbarred triple; the embedded input marker
is the barred triple. Section 5 below adds the one required transport.

## 3. Right liberation pi

Use a fresh A and two distinct fresh letters x,x', imposing only

    d^x=d, e^x=e^2;
    d^x'=d_-1, e^x'=e^2.

The notation d_-1 means e*d*e^-1. Form B=K *F A*, where A* has eleven
names and twenty-four relators. Its distinct base list X_B has g+8 names,
including all input names once, six new A auxiliaries and x,x'. Append

    v1 fixes L;
    v2 fixes (d_1,x,x');
    v3 fixes (X_B^v1,X_B^v2);
    v4 fixes (a,b,c);
    Lpi=X_B^(v3*v4).

The positive seed is d_1=e^-1*d*e. The two maps give d_i^x=d_(2i)
and d_i^x'=d_(2i-1), consistent with primary (6.13)'s positive-index
subgroup. The equality A intersect <d_1,x,x'>=<d_j:j>=1> and its use
in the amalgam remain the stated Section 6.8 premise. Signed powers of
d_j alter coordinate values with either sign; they do not free negative
coordinate indices.

The count is g+12,r+2g+l+46,list(g+8). The marker is unchanged, so no
transport letter is added. Do not repeat the common a,b,c in X_B: the
normalized specification removed precisely the six redundant centralizer
relations present in the primary's larger displayed pi count. Do not
remove any additional equal-looking relation or letter.

## 4. Every literal family in D_d and omega_d

Here d is a positive block size, not a generator name or input size. Begin
with the eight distinct names b,c,Td,Td',T0,T0',r1,r2 and these fourteen
relators:

    (b,c)^Td  = (b_(1-d),c^2);
    (b,c)^Td' = (b_-d,c^2);
    (b,c)^T0  = (b_1,c^2);
    (b,c)^T0' = (b,c^2);
    r1 fixes (b_d,Td,Td'); r2 fixes (b_-1,T0,T0').

Adjoin g0,h,k, each fixing the four words b^r1,c^r1,b^r2,c^r2. Call the
result G_d, with ordered eleven-name list X_G and twenty-six relators.
Put h_i=k^-i*h*k^i. For every 1<=s<=d and 0<=j<s, adjoin lambda_(s-1,j)
with exactly s+2 matched equations on (b_(s-1),g0,h_0,...,h_(s-1)):

    b_(s-1) -> b_(s-1),  g0 -> g0^h_j,
    h_i -> h_i^h_j if i<j;  h_i -> h_i if i>=j.

These are maps of the indicated free subgroup, not extra equations on
the other G_d generators. Next p0 fixes g0, and for each s=1,...,d,
p_s fixes the s+1-word list

    (g0^h_(s-1))*b_(s-1)^-1*g0^-1,
    lambda_(s-1,0),...,lambda_(s-1,s-1).

The first expression's order and scope of its conjugate matter. It is
not the conjugate of the whole product by h_(s-1). Adjoin a fixing
X_G^p_i for every i=0,...,d, exactly 11(d+1) words. In particular this
list contains the eleven G_d names, not all lambda or p names. Finally
adjoin q with the three equations

    a^q=a, b^q=b^(c^d)=b_d, c^q=c.

This defines D_d. With D=13+(d+1)(d+2)/2, its exact sizes are

    names D;
    relators 26+sum[s(s+2)] +1+sum[s+1]+11(d+1)+3
             =41+(d^3+6d^2+41d)/3,

where both sums range over s=1,...,d. All these literal families match
primary (6.36),(6.43)--(6.46), with the previously retained arithmetic
and fresh-letter corrections. Visual pages 46 and 49 disambiguate the
conjugations g0^h_j, g0^h_(s-1) and b^(c^d).

Rename the input marker to g0,h,k and amalgamate that one input copy with
D_d over those three names. No other input name is identified with D_d.
With four further fresh letters, append

    q1 fixes L_input;
    q2 fixes (a,q);
    q3 fixes (X_D^q1,X_D^q2);
    q4 fixes (a,b,c);
    Lomega=X_D^(q3*q4).

Here X_D is precisely the D distinct names of D_d, not the entire
amalgam's generator list. The old marker is g0,h,k; the new one is a,b,c.
The raw wrapper count is g+D+1,r+l+74+(d^3+9d^2+50d)/3,listD.
Adding Section 5's transport gives g+D+2 and r+l+77+(d^3+9d^2+50d)/3.

For d=1 no empty-range exception or unsupported limit is used: the source
explicitly displays lambda_00 on b0,g0,h0. The literal D_1 list is

    b,c,T1,T1',T0,T0',r1,r2,g0,h,k,lambda00,p0,p1,a,q.

It has sixteen names and 14+12+3+1+2+22+3=57 relations. The entire
persistent omega_1 update is +18 generators, +(l+97) relators, list16.
The input N is one-supported and contains zero. The other actual inputs
U0 and R_bare likewise are block-supported and have explicit zero blocks.
The corrected zero-containing hypothesis of primary Lemma 6.4 is retained.
The whole lemma, including its nested-normal-form reverse inclusion, is
still an imported premise; this syntax audit does not newly certify it.

## 5. Marker, cached list, initial A and shift transport

For a marker-changing wrapper let phi be its explicit input embedding
(barred copy for rho, g0/h/k roles for omega). After the wrapper append
one fresh t with exactly

    phi(a)^t=a_out, phi(b)^t=b_out, phi(c)^t=c_out.

Both triples are bases of free rank-three subgroups under the imported
wrapper premises. HNN normal form preserves the whole wrapper group.
For every previously stored list L_j, replace it by phi(L_j)^t. The new
wrapper-output list is excluded from this update. Then

    F_out intersect <phi(L_j)^t>
      =(F_in intersect <phi(L_j)>)^t=A_(E_j).

Apply the same whole-word operation to all nine images of the tracked
initial A and to the tracked shift word. A stored image may be a long
conjugate rather than a generator ID. In particular its a,b,c images need
only be equal to the new literal marker by the three transport relations;
they need not be syntactically those three IDs. Affine-list generation
must consistently use that tracked copy, or use these proved equalities.
Fresh local auxiliary A letters are not substitutes for its d,e images.

The initial shift word s obeys a^s=a,b^s=b^c,c^s=c. Its transported word
is phi(s)^t, and conjugating these three identities proves the same law
at the new marker. Consequently L^(s^k) implements sigma^k for signed
fixed k; there is no new shift letter and no change of list length. Pi
keeps the marker, so its input embedding alone carries all stored data.
The final two-relator transducer keeps the marker and all old data; it
is a separate construction and receives no generic unary transport.

## 6. Retained hazards, downstream boundary and scope

**Remark 1 (identical maps do not identify letters).** For d=1, T1 and
T0' both display (b,c)->(b,c^2), but are distinct stable letters in the
two boundary constructions. No alias or generator deletion follows. The
sixteen-name D_1 list and its centralizer families retain both letters.

**Remark 2 (reflection is not a commuting-word rule).** Reflecting the
indices of a sorted d-word reverses their order. The signed-action lemma
gives the required action on a_f, not equality after commuting d_i in
the free stable-letter subgroup. Treating those literal words as abelian
would destroy the fixed-A retraction and later free-pair arguments.

**Remark 3 (primary naming and counts remain corrected).** The prior
normalized note retains pi's x1/x2 versus x1/x1' slip and duplicated marker
relations; omega's nonintegral generator simplification, overlap of the
renamed input marker, and t2 versus p2 in (6.38); and the missing zero
hypothesis with a concrete counterexample. This audit uses those explicit
repairs and does not silently adopt the erroneous printed alternatives.

**Remark 4 (later embedding is a different, defective premise).** Root's
separate `review_higman_section7_noninjective_root.md` proves that the
printed product family v*w cannot be isomorphic to the indexed free family
u^(z^w), and that (7.10)'s finite relations kill an explicit nontrivial
base word. I independently confirmed its source notation, kernel word,
finite conjugation orientation and full written proof. The historical
20808/34232/37937/49792 downstream values are formal slot counts, not
certified faithful embedding sizes. This failure does not alter the
preembedding recipes audited above; frozen parents are retained.

The exact current primary reads are LF1240--1328,1547--1735,1868--2017,
2379--2810 and2935--3135, plus visual pages46,49,53. The final downstream
proof and local frozen recipe/core/schedule texts were read as recorded in
the receipt. Earlier broader reads are not counted as new work here.
No supplied or frozen helper, group-word program, presentation expander,
scientific array, symbolic evaluator, coefficient computation or build was
executed. Only ordinary PDF reading/rendering and fresh byte metadata are
used. Root independently read the complete specification and passed without
correction: every wrapper word family, the d=1 boundary, role renaming,
base-list scopes and whole-word persistent transport were checked. The
proof/specification and its receipt are frozen after this provenance-only
update. Its downstream correction is bound at immutable commit
7b4551b245e05018b4cb3880151e7447aedb7fa3; no predecessor was rewritten.
