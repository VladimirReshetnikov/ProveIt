# K/S with mixed double-negation commutation: a refutation translation

Author: review_upstream_reflection, 20 October 2026. This is an ordinary
all-natural proof proposal, with a finite Hilbert check of the main local
bridges. It is not a Lean theorem or a binary-machine construction.

## The two precise calculi

Let C be the accepted Code254/KCode222 numerical calculus: native truth
0, MP, theorem-only GEN, rho1–rho6, merged G, unrestricted rho8 and the
literal gated bundle. Use I, R, E, Q for the native constructors; F=1,
N A=I(A,F), D A=NN A. All arguments and labels are arbitrary natural
numbers. The native alias I(0,0)=0 is retained.

Define C_M by retaining every one of those rules/rows except rho4 and
rho8. Replace rho8 by the two K/S schemas, and replace rho4 by

    M(i,j,A): Q_i D(Q_j A) → D(Q_j(Q_i A)).

This is one unrestricted three-parameter row, with no new gate. There is
no QS axiom, no ordinary formula-substitution rule, and no extra quantifier
elimination rule. The original literal bundle, including c≠a,b and the
matrix/private-label identity m=k=c, remains unchanged.

Claim: there are primitive-recursive finite-refutation translations in
both directions between C and C_M. Hence their consistency statements are
equivalent, with the equivalence formalizable in PA. This is refutation
equivalence, not a claim of pointwise identical derivable codes.

## Already available intuitionistic infrastructure

The earlier K/S-only derivations in Source 144 and the repository's
K/S+QS proof establish the following without using either QS or rho4:

* explosion F→A from K/S and rho6;
* seriality Q_i F→F from rho1, rho2 and theorem-only GEN;
* membership and equality stability D R(a,b)→R(a,b) and
  D E(a,b)→E(a,b), using the exact gated bundle and merged G;
* stability of A→B whenever B is stable.

The membership proof chooses c=max(a,b)+1, uses the negative bundle to
derive double-negated membership persistence, and then the retained B6
rho6 argument. The equality proof uses existential monotonicity, rho1,
merged G and B6. Every necessity/GEN step in these arguments acts on a
closed theorem. The earlier finite checker does not even offer rho4 as an
axiom kind in this infrastructure. Its QS-dependent final code induction
is not being reused here.

K/S deduction, explosion and normality justify all intuitionistic arrows
below. In particular, from a closed X→Y we may derive Q_i X→Q_i Y,
D X→D Y and N Y→N X. We may replace equivalent bodies beneath Q by
two applications of normality. The identities N(D X)↔N X and
D(D X)↔D X are intuitionistic, not a use of arbitrary DNE.

## Co-translate labels as well as formulas

Define τ by strong recursion on actual natural codes:

    τ(0)=0
    τ(I(a,b))=I(τa,τb)
    τ(R(a,b))=R(τa,τb)
    τ(E(a,b))=E(τa,τb)
    τ(Q_i A)=D(Q_(τi)(τA)).

The first line is used before decoding a positive code. Every argument of
a positive constructor is smaller than its code. Thus bounded
course-of-values recursion defines a primitive-recursive total function.
The displayed I equation also holds at the zero alias, because
I(τ0,τ0)=I(0,0)=0. In particular τF=F and τ(N A)=N(τA).

Unlike an atom-fixed negative translation, this map preserves the literal
couplings: τ(R(a,b)) is exactly R(τa,τb), and the matrix c and its private
binder both become τc. No arbitrary renaming theorem is invoked.

### Injectivity and gates

No τ-image has outer tag Q: its possible tags are I, R and E. Moreover
no τ-image is N(Q_i X). For an I-source this would require its translated
left child to be Q-headed. For a Q-source the translated left child is
I-headed, whereas N(Q_i X) has a Q-headed left child. R/E tags disagree,
and zero cannot equal this positive implication. These are literal
constructor inversions, not propositional equivalences.

Also τn=0 implies n=0, by strong induction: positive R/E/Q sources map
to positive codes; an I-source can map to zero only when both translated
children are zero, hence both source children are zero.

Now prove injectivity by strong induction on m+n in τm=τn. Separate
zero first. R/E sources are recognized by their tags and reduce to
strictly smaller pairs of arguments. Two I sources reduce by I
injectivity; two Q sources reduce through the two explicit negations and
the inner Q constructor. An I/Q collision is impossible: the translated
I left child is itself an image, while the translated Q left child is
N(Q_i X), which is not an image. All other mixed cases have different
tags. Hence τm=τn implies m=n. In particular c≠a,b entails
τc≠τa,τb, so original gates remain valid.

### Every translated code is stable

Strong induction on n gives a C_M proof of D(τn)→τn. Zero is a theorem.
Translated R/E atoms use the previously derived atomic stability at the
translated numeric labels. A translated quantifier is D X, which is
intuitionistically stable. An implication uses stability of its translated
consequent. This induction does not assert stability of arbitrary
untranslated quantified codes and does not use QS.

## Translating the logical rows

Truth and MP transport literally, including the zero alias. From a closed
proof of τA, GEN at the actual label τi gives Q_(τi)τA; double-negation
introduction gives τ(Q_i A). No open hypothesis is generalized.

For the rows below write α=τa, β=τb and so on.

* rho1 translates to N D Q_α N E(α,β), equivalent to the retained
  rho1(α,β) by N D X↔N X.
* rho2 translates to
  D Q_α(β→γ) → (D Q_α β → D Q_α γ).
  Double-negation monotonicity applied to native rho2, followed by the
  intuitionistic preservation of MP under D, proves it.
* rho3 and rho5 translate exactly to their native instances at mapped
  parameters, since only implication and atoms occur.
* rho6 translates to N D Q_α N D Q_α β → β. Replacing N D X by N X
  first at the outer negation and then under the inner Q makes this the
  retained rho6(α,β).
* merged G translates to its native instance with only the quantified
  consequent replaced by its double negation. Native G and
  double-negation introduction prove that instance. Its binder is exactly
  R(α,β), by the co-translation law.
* rho8 translates to rho8(τa,τb,τc,τu). The finite intuitionistic
  conditional theorem `(D C→C)→rho8(A,B,C,U)` from the previous proof,
  together with stability of τc, supplies it. All four numeric parameters
  remain independent.

Only the original rho4 needs the new M row. Its translation is

    D Q_α D Q_β γ → D Q_β D Q_α γ.

Apply double-negation monotonicity to M(α,β,γ) and eliminate D D on its
consequent, obtaining

    D Q_α D Q_β γ → D Q_β Q_α γ.

Normality applied to Q_α γ→D Q_α γ, then double-negation monotonicity,
gives the required final implication. Old rho4 is not needed anywhere in
this argument or in the atomic-stability infrastructure.

## The exact seed bundle translates

This is a one-way derivation from the native bundle at the mapped
parameters, not an assumption that negative translation commutes with Q.
For this section a,b,c denote those already mapped parameters. All
occurrences of the matrix/private code are literally c. Put

    B = req(b,c,c)
    S = Q_c(R(c,a) → R(c,b))
    X = S → B
    C = clos(a,b,c,c)
      = Q_b(R(b,c) → N Q_a(c → N Q_a X))
    Z = C → N B
    J = Q_c Z
    V = R(a,b) → Q_c R(a,b).

The available native bundle is N(V→J). In its translated syntax, normalize
only N D Y↔N Y, transporting these closed equivalences through implication
and Q. The translated expressions then are equivalent to

    B* = D B,        S* = D S,        X* = D S → D B,
    C* = D Q_b(R(b,c) → N Q_a(c → N Q_a X*)),
    Z* = C* → N(D B),     J* = D Q_c Z*,
    V* = R(a,b) → D Q_c R(a,b),
    translated bundle = N(V* → J*).

For B*, the literal req formula is
`Q_b(c→N Q_b(c→N R(b,c)))`; its inner inserted D is immediately under N.
The same cancellations produce C* above while retaining **both** repeated
Q_a operators. The outer quantified subformula S and req B remain under
D; they are not silently simplified to S or B.

The intuitionistic theorem X→X* gives Q_a X→Q_a X*. Contraposition,
implication monotonicity with antecedent c, normality, and contraposition
again give

    N Q_a(c→N Q_a X) → N Q_a(c→N Q_a X*).

There are two order reversals, so the direction is as displayed. Extend
through R(b,c)→..., Q_b and D-introduction to obtain C→C*.
Together with N(D B)→N B, this gives Z*→Z. Normality and D-monotonicity
therefore give

    J* → D J.

Native N(V→J) intuitionistically supplies D V and N J. The elementary
V→V* gives D V→D V*. From N J and J*→D J, obtain N J*. Finally
D V* and N J* give N(V*→J*): an assumed V*→J* would imply N V*,
contradicting D V*. This is the required translated bundle.

This argument needs neither stability of the arbitrary matrix c nor a
fresh-parameter rewrite. Co-translation already made the matrix and binder
agree, and injectivity supplies the original gate. It even proves the
conditional bundle bridge for arbitrary mapped parameter values.

## Both finite-refutation translations

Induct on a finite C derivation. Translate its code labels with τ and use
the constructions above at each axiom, MP or GEN node. An original bundle
node uses the native C_M bundle at τa,τb,τc, with gates preserved by
injectivity, followed by the conditional bridge. A derivation of F thus
becomes a C_M derivation of τF=F.

Conversely, C proves K and S by its accepted classical basis. It proves
M(i,j,A): classical DNE transforms Q_i D(Q_j A) to Q_i Q_j A by
normality, rho4 gives Q_j Q_i A, and D-introduction gives the required
consequent. These steps apply to arbitrary actual natural codes. Every
other C_M axiom/rule is retained literally in C. Replacing each new axiom
node by these fixed proof constructions translates any C_M refutation to C.

Decoding, co-translation, the atomic-stability construction, native gate
transport and finite Hilbert-DAG operations are primitive recursive.
Strong induction on natural codes and on finite derivations proves their
correctness in PA. Therefore this is an explicit ordinary consistency
calibration; it is not merely the failure of a finite countermodel search.
Combining with the accepted calibration of C yields the corresponding
consistency equivalence with ZFC. An actual smaller machine still requires
the exact new enumerator, source/table compilation, unbounded primitive
simulation and complete startup proof.

## Checks, attribution and limits

`check_bridges.py` uses a byte-exact copy of Opening's reviewed finite
Hilbert checker as a library. Its first run checked 1,364 nodes and seven
closed outputs, including the two literal negation normalizations, the
closure/core/bundle arrows and M-to-translated-rho4. The only axiom schemas
used are K, S, rho2 and rho6. Every GEN is closed; M and the native bundle
are discharged hypotheses in these conditional bridge theorems. No QS,
old rho4, supplied wrapper or proof assistant was run. The ordinary
all-natural co-translation and proof-induction arguments are above; the
finite executable check does not itself establish those metatheorems.

Source 144 supplied the K/S-only atomic-stability lemmas and two modal
counterexamples; Opening made their finite Hilbert implementation explicit
in the K/S+QS packet. Root suggested co-translating the numerical labels
and replacing rho4 by a mixed row, and independently checked the bundle
signs. This note supplies the injective delimiter argument and the complete
refutation translation with the literal bundle bridge.

The original K/S-only proposal remains unresolved here. The nine-element
modal counterexample still blocks a generic proof that D-Booleanized
commuting Q operators commute. It is only a modal-subtheory example, not a
model of the full native bundle, and does not refute a special argument
for stable-coded labels. This positive result avoids that open obligation
by changing rho4 to M, rather than assuming the missing commutation.
