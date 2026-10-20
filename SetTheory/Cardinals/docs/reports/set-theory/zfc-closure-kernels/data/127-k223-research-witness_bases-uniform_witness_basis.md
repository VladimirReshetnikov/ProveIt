# A helper-free logical basis using uniform equality witnesses

## Result and scope

There are two calibrated replacements for the logical part of the exact K224
numerical calculus. Neither simply deletes the equality helper from the old
logic. Both replace the old equality-existence row by a stronger row, and
neither needs primitive equality reflexivity.

Let P(a,b)=(a+b)(a+b+1)/2+b and let kappa(a,b)=4P(a,b)+1 (the Rel-code
builder), or =4P(a,b)+3 (the Eq-code builder). Both strictly exceed a,b,
including (0,0). Keep numerical implication, F=1, N(A)=I(A,F),
And(A,B)=N(I(A,N(B))), Ex_i A=N(All_i N(A)), truth seed 0, MP, and closed
GEN. Keep rho2, rho3, rho4, rho5, rho6, rho8 and full gated membership
vacuity. Keep the exact K core, actual matrix/private code c, and gate
c!=a,b. Delete the separate primitive equality-vacuity helper.

Variant A replaces rho1 and rho7 by

    UW(a,b): Ex_a All_{kappa(a,b)} Eq(a,b),
    SYM(a,b): Eq(a,b) -> Eq(b,a).

Variant B uses only

    SUW(a,b): Ex_a All_{kappa(a,b)}
                   (Eq(a,b) AND Eq(b,a))

in place of rho1 and rho7. There is no primitive symmetry row in B.

Each resulting numerical calculus is equiconsistent with ordinary ZFC,
by a uniform finite-proof interpretation into membership indiscernibility
and the existing exact K matrix/code coupling argument. This is an ordinary
mathematical proof, not a new compiled Rocq endpoint. A changed source or
machine must separately bind the exact rows and verify enumeration, runtime,
blank initialization, and state count. No state saving is implied here.

The important distinction is uniformity of the witness. We do not prove
Eq(a,b)->All_kappa Eq(a,b), and do not silently retain the old rho1 as a
primitive row.

## 1. Common notation and retained logical rows

Write G(a,b)=Eq(a,b) in A and G(a,b)=Eq(a,b) AND Eq(b,a) in B. The new
existence row is Ex_a All_kappa(a,b) G(a,b).

The literal retained rows are

    rho2(i,A,B): All_i(A->B) -> (All_i A -> All_i B)
    rho3(a,b,c): Eq(a,b) -> (Rel(c,a) -> Rel(c,b))
    rho4(i,j,A): All_i All_j A -> All_j All_i A
    rho5(a,b,c): Eq(a,b) -> (Rel(a,c) -> Rel(b,c))
    rho6(i,A): Ex_i All_i A -> A
    rho8(a,b,c,u): (((c->u)->a) -> ((a->c)->(b->c))).

These agree with Codes230.v modulo harmless argument order for rho5.
Rho8 supplies K/S/Peirce by the pinned CD230 derivations; rho6 supplies
explosion F->A without rho1 or vacuity. Thus all classical propositional
tautologies with designated F are derived abbreviations. In particular
closed universal and existential monotonicity use only rho2, GEN and
propositional reasoning.

The proof manipulates a designated bottom alias F. Quantifier-free
renaming fixes that alias, even though its numerical representation is
Rel(0,0). Explosion gives F->All_i F for every i, including 0. It is
incorrect to regard a raw renaming of Rel(0,0) as the bottom-renaming rule.

## 2. Seriality without old rho1

For every i put B_i=All_{kappa(i,0)} G(i,0). The new row supplies Ex_i B_i.
The tautology F->not B_i, generalized and distributed, gives

    All_i F -> All_i not B_i.

The latter contradicts Ex_i B_i. Therefore

    All_i F -> F.                                          (SER)

This uses no universal instantiation, no existential elimination, no
primitive equality theorem, and no freshness assertion about B_i.
In particular it is valid at i=0 and kappa(0,0)=1 or 3.

## 3. Membership-only vacuity and vacuous universal elimination

For every membership-only formula A and every i absent from all its
syntactic labels, derive

    A -> All_i A.                                          (VAC)

The existing structural proof uses membership-atom vacuity, propositional
reasoning, rho2 and rho4. In the designated-bottom branch use explosion.
Its implication branch first obtains vacuity for negation: from VAC,
existential monotonicity and rho6 yield Ex_i A -> A, whose contraposition
is not A -> All_i not A. Its quantifier branch commutes the two different
binders using rho4. No equality existence is used by this induction.

For the same fresh A, (VAC) also gives

    Ex_i A -> A,                                           (VE)
    All_i A -> A.                                          (VU)

VE is exactly existential monotonicity applied to VAC followed by rho6.
For VU, not A implies All_i not A as above. All_i A and All_i not A give
All_i F by rho2, contradicting SER. Classical reasoning discharges not A.

The proof needs only syntactic absence, a stronger side condition than
ordinary free-variable freshness. Later choices ensure this stronger
condition explicitly. No native alpha-conversion rule is assumed.

## 4. Quantifier-free specialization, including helper-binder collisions

Let f be a quantifier-free membership/designated-bottom formula, x!=y,
and g=f[y/x] replace x by y while fixing designated bottom.
Atomic rho3/rho5 and propositional induction give

    G(x,y) -> (f -> g),
    G(x,y) -> (g -> f).                                   (LEIB)

In A the reverse direction uses its explicit SYM row. In B both directional
Eq premises are projections of G, so there is no primitive symmetry use.
No quantified Leibniz principle is invoked.

First suppose k=kappa(x,y) is absent from f and g. GEN_k and rho2 applied
to LEIB give

    All_k G(x,y) -> All_k(f->g).

VU for the membership-only formula f->g reduces this to

    All_k G(x,y) -> (f->g).

Shuffle propositionally, GEN_x and distribute. Existential monotonicity
inside that universal implication and the new witness row yield

    All_x f -> Ex_x g.

The formula g has no x, apart from the designated-bottom alias, so VE gives

    All_x f -> g.                                         (FRESH-SPEC)

All GEN operations above generalize closed implications. In particular
there is no GEN under an undischarged equality or formula premise.

For arbitrary x,y and f, including x=y and cases where kappa(x,y) is a
label in f, choose

    z = 1 + max({x,y} union all labels occurring in f).

Apply FRESH-SPEC from x to z. Its helper kappa(x,z)>z is absent from f and
f[z/x]. The result is All_x f -> f[z/x]. Since z is absent from All_x f,
VAC plus GEN_z/rho2 yields

    All_x f -> All_z f[z/x].

Apply FRESH-SPEC from z to y. Its helper kappa(z,y)>z and >y is absent
from f[z/x] and its target. Because z was wholly fresh, the final target
is exactly f[y/x], even when x=y. Hence unrestricted quantifier-free
specialization is derived by a two-step fresh detour.

The detour is needed: one cannot assume kappa(x,y) is fresh in an arbitrary
membership formula just because it exceeds x and y.

## 5. Interpreted equality

For z distinct from a,b let

    L_ab(z) = (Rel(z,a)->Rel(z,b)) AND (Rel(z,b)->Rel(z,a)),
    U_ab(z) = (Rel(a,z)->Rel(b,z)) AND (Rel(b,z)->Rel(a,z)),
    E_ab^z = All_z L_ab(z) AND All_z U_ab(z),
    E(a,b) = E_ab^{EqCode(a,b)}.

The quantifier-free specialization of Section 4 and membership-only VAC
now prove all the Source116 auxiliary-transport and E-law constructions:

- E_ab^z -> E_ab^w for either safe auxiliary (and its reverse).
- E(a,b)->All_i E(a,b) whenever i!=a,b, including i=EqCode(a,b).
- Both membership-congruence rows with E replacing Eq, including every
  parameter coincidence and label 0.
- E(c,a)->(E(c,b)->E(a,b)), as well as E reflexivity and symmetry.

For completeness, transport specializes each quantified L/U from z to w,
then generalizes at w using VAC of its premise; E-vacuity transports first
to w above a,b,i and both old auxiliaries. E-membership congruence transports
to w above the requested third label before specializing. E-Euclid
transports both premises to one wholly fresh w and combines the Boolean
transitivity tautologies under All_w. Every step uses only the membership
language and closed GEN.

The remaining interpreted rho1 follows directly from uniform witnesses.
Atomic congruence in both directions gives G(a,b)->L_ab(k) and
G(a,b)->U_ab(k), where k=kappa(a,b). GEN_k/rho2 therefore gives

    All_k G(a,b) -> E_ab^k.

Existential monotonicity and UW/SUW give Ex_a E_ab^k. Apply existential
monotonicity once more to auxiliary transport from k to EqCode(a,b):

    Ex_a E(a,b).                                          (E-EX)

No primitive equality reflexivity, primitive equality vacuity, old rho1,
or general existential-witness elimination occurs.

## 6. All first-order logical proofs translate

Translate genuine ordinary equality Eq(a,b) to E(a,b), genuine bottom to
F, and preserve membership, implication, and every universal label.
Sections 2--5 provide the translated rho1, rho3, rho5, rho7 and equality
vacuity of the complete original Tarski calculus. Rho2/rho4/rho6/rho8 and
membership vacuity translate to retained schemas. MP and closed GEN commute
literally with the translation. Induction on finite proof trees supplies a
uniform effective logical proof interpretation.

The replacement axiom UW/SUW itself need not be translated into the old
calculus for this direction. It is the tool used to derive every *old*
logical axiom after the E interpretation.

## 7. Exact K matrix/private-code coupling and consistency

The logical interpretation uses no set-theoretic axiom. Therefore the exact
argument in portable/theory/k_equality_helper_extension.md applies with
Sections 2--6 replacing its helper-based logical premise:

1. Choose a hygienically named ordinary K matrix f, input label 1, output
   label 3, odd parameter names and positive even bound names.
2. Interpret its equality to obtain psi=theta(f).
3. Put pp=not not psi and c=encode(pp). Then c>3 and every label of pp is
   strictly below c. The latter is the direct constructor-code induction,
   not a decoded-low-code assertion.
4. Choose the ordinary comparison K axiom's private name to be this c,
   after translating the matrix. The K skeleton contains no equality and
   commutes with theta. Its interpreted matrix is pp with literal code c.
5. The result is exactly the native kcore(1,3,c,c), projected from the
   enabled K/membership bundle. Both gate inequalities hold.
6. Translate the finite ordinary K+IR refutation. The interpreted IR is
   All_0(F->F), a generalized identity. The final bottom is exactly F=1.

This yields not Con(ZFC) -> derivability of F using the existing ordinary
K+IR calibration. Fusion of redundant negative constructors changes no
part of the argument, by the existing closed fusion proof.

Conversely UW is valid in genuine equality semantics: choose the current
value of b as the a witness, and kappa(a,b) is different from a,b. SUW is
valid for the same reason. SYM is valid. All remaining rows and K instances
are old valid instances, so the existing relative-falsity/zero-code soundness
translation gives Con(ZFC) -> no numerical derivation of F.

The numerical exceptions are handled exactly: 0 remains the truth seed;
1 is both F and Rel(0,0), validated as relative bottom using IR. The lower
K proof uses c>3, never an arbitrary low matrix/private collision. The new
UW rows use Eq atoms of code >=3 and All constructors, so their only
implications into code 1 are the intended negative existential/conjunction
encodings. For a=b=0, kappa is 1 or 3 and the witness formula is an ordinary
true equality assertion. There is no 0/1 decoder substitution assumption.

All constructions are finite syntax/proof transformations with explicit
max-plus-one fresh names. They can be formalized in ordinary ZFC. This is
stronger than merely comparing external truth in standard models, but it
is not claimed to have been compiled in a proof assistant here.

## 8. Other constructor binders

The proof extends to any computable kappa with two properties:

- kappa(a,b) differs from a,b when a!=b;
- for each finite bound B and endpoints x,y<=B there is an effectively
  chosen z>B such that kappa(x,z) and kappa(z,y) exceed B,z.

All eight native Imp/Rel/All/Eq builders in either argument order satisfy
these properties. Positive tags also make every diagonal safe. Imp has
kappa(0,0)=0; in that sole unsafe diagonal case use the theorem E(0,0)
and seriality/existential monotonicity to derive Ex_0 E(0,0), rather than
forming the ill-bound E_00^0. Soundness remains immediate because Eq(0,0)
and its universal closure are true. The current finite certificates focus
on positive Rel/Eq tags and do not certify this optional branch.

## 9. Verification boundary

The ordinary proof above is the uniform theorem. Independent proof-local
replays check finite numerical instances of its bootstrap, fresh-detour
specialization (including deliberate kappa collisions), label 0, diagonal
pairs, internal-auxiliary E-vacuity and E-congruence/Euclid. Their TAUT leaves
are Boolean-checked classical tautologies, abbreviating the retained
rho8/rho6 basis; no old rho1 or equality-vacuity leaf is accepted. The
symmetric-witness replay additionally forbids SYM.

These checks do not prove arbitrary-label induction, the ordinary K/ZFC
calibration, exact source printing, state savings, or a new compiled formal
endpoint. See the separate receipts and source-pricing work for those
boundaries.

## 10. Cheaper placement: put the witness in the existing gated bundle

The standalone witness row is not necessary. Instead print

    KCore(a,b,c,c) AND RelVac(a,b,c) AND Ex_a All_c G(a,b)

under exactly the existing gate c!=a,b, and omit standalone rho1. In A,
retain separate primitive SYM; in B omit both rho7 and SYM. For every a,b,
choose c=RelCode(a,b)>a,b. Propositional projection gives exactly UW/SUW
with that canonical kappa. The proof above applies unchanged. Every
printed witness conjunct is valid in ordinary equality under its gate,
so soundness also applies unchanged. The K matrix/private label remains
the actual opaque c and is not reinterpreted as a separately chosen fresh
code by the source.

This placement avoids computing the canonical witness-binder arithmetic
inside rho1. It changes the number/order of proof-stack slots emitted by
AX and therefore requires an explicit enumerator adaptation. Logical
soundness and completeness do not establish that source-level adaptation.

## 11. What remains open about bare deletion

This result does not settle whether full K itself repairs the old logic
when the Eq-helper is deleted and rho1/rho7 are left unchanged. The earlier
colored-graph counterinterpretation proves only failure of membership-only
logical completeness in the logical fragment. It is not a full K model.

Indeed the graph also refutes an exact native K instance, not merely CP.
Take a=2,b=3,c=1. Its opaque matrix is F=Rel(0,0), false everywhere in that
irreflexive graph interpretation. The K support clause then requires its
outer label-1 container to have no label-3 member, since every member
would need an input witness satisfying F. But the graph's countable
extension property supplies a label-3 vertex adjacent to every proposed
label-1 container. Thus literal KCore(2,3,1,1) is false, and the native
gates 1!=2,3 pass. This uses the actual matrix/private code 1 without any
renaming. It does not apply to conditional K's false-root instance, and
is not needed by the successful uniform-witness argument.

Consequently bare helper deletion still lacks either a full-K calibration
or a full-K obstruction here. The successful route changes the equality
witness axiom so its logical bootstrap is provable independently of K.

For the canonical standalone variants, there is also a direct old-calculus
soundness comparison. K224's original Rel-code helper and rho1 give
Ex_a All_RelCode(a,b) Eq(a,b) by existential monotonicity; its checked
symmetry theorem supplies SYM. Quantifying that symmetry implication and
conjoining under the same binder gives the symmetric-witness row as well.
This observation concerns canonical standalone witnesses only. It does not
claim that the old restricted-helper calculus proves arbitrary-c witnessed
rows in the gated placement; the latter's upper consistency direction is
its ordinary-equality soundness proof above.
