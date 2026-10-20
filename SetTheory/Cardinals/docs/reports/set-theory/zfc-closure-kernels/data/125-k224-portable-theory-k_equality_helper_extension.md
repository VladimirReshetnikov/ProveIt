# Restricted equality vacuity transfers to the current K family

## Precise statement

Retain the current K230/K225 numerical constructors, truth seed 0,
rho1--rho8, MP, theorem GEN, and full gated membership vacuity. In the
set-theoretic bundle replace only

    Eq(a,b) -> All_c Eq(a,b)

by

    Eq(a,b) -> All_{kappa(a,b)} Eq(a,b),                 (H_kappa)

where kappa is a computable native-label builder satisfying

    a != b implies kappa(a,b) != a and kappa(a,b) != b.

No condition is imposed on kappa(a,a). Keep the original gate c!=a,b
and the original K core with actual matrix/private code c. The resulting
numerical calculus is equiconsistent with ZFC. The same theorem holds if
the core has been changed to the calibrated conditional K schema.

This uses the genuine restricted-helper proof in Source 116 together
with the new K-specific matrix/binder coupling argument below. It is NOT
an automatic reuse of Source 116's old CP/GIC set-theory endpoint.
No state count follows until the changed source and machine are checked.

Admissible choices include all eight native builders

    Imp(a,b), Imp(b,a), Rel(a,b), Rel(b,a),
    All(a,b), All(b,a), Eq(a,b), Eq(b,a).

The implication builders have the sole low-label collision
kappa(0,0)=0; it is an allowed diagonal case. Positive-tag builders are
strictly larger than both arguments.

## 1. The logical interpretation supplied by Source 116

The relevant primary retained files are

    data/116-eqred-proofs-general_kappa_equality_helper.md
    data/116-eqred-audit-mathematical_audit.md

in ProveIt's zfc-closure-kernels report corpus. Their logical bootstrap
does not use CP, GIC, K, or any other set-theoretic axiom. It uses only
rho1--rho8, membership vacuity, the helper H_kappa, MP, and closed GEN.

For names a,b choose the fixed safe auxiliary

    z = EqCode(a,b) = 4 P(a,b)+3 > a,b

and define membership indiscernibility

    E(a,b) :=
      [forall z (R(z,a) iff R(z,b))] and
      [forall z (R(a,z) iff R(b,z))].

Each biconditional and conjunction is expanded in the retained classical
relative-falsity syntax. The choice of the quantified auxiliary is part
of the actual formula. It may coincide with some unrelated name, but
never with either of the two endpoints.

The finite logical proof establishes all translations of the full
original first-order equality calculus when primitive Eq(a,b) is replaced
by E(a,b), genuine bottom is sent to F=Rel(0,0), and membership,
implication, and every universal binder are preserved. In particular:

- Membership-only fresh vacuity is proved by induction on formulas.
- The specializations needed by E are first proved for quantifier-free
  membership matrices; no general substitution rule is assumed.
- Different safe auxiliary labels in E are connected by explicit finite
  transport proofs using fresh maxima plus one.
- The full translated E-vacuity and membership-congruence rows hold for
  all coincidences, including label 0 and the case in which a requested
  quantifier equals E's internal auxiliary label.
- E-reflexivity, symmetry, and the translated ternary rho7 hold.
- H_kappa first bootstraps primitive reflexivity and symmetry if needed.
  Off-diagonal helpers give Eq(a,b)->E(a,b) by safe auxiliary transport;
  on the diagonal E(a,a) is a membership-identity theorem.
- Rho1 and existential monotonicity then give Ex_a E(a,b), the
  interpreted equality-existence row.

All these are effective syntactic derivations. The source has every
H_kappa(a,b): choose any original c different from a,b and project the
helper from its bundle. It is unnecessary and sometimes incorrect to
choose c=kappa(a,b).

The resulting logical proof interpretation has only MP and GEN as
inference constructors. It does not need its formula translation to
commute literally with arbitrary substitution or alpha conversion; all
logical proofs are translated using the explicit translated axiom
derivations. This matters because E's numerical auxiliary changes when
its endpoint labels change.

## 2. The new actual-code coupling argument for K

Let f be a finite genuine-bottom named formula representing an arbitrary
ordinary K matrix. Choose input name 1, output name 3, distinct positive
odd parameter names, and positive even bound names. Let theta be the
logical interpretation from Section 1, and form

    psi = theta(f),
    pp  = not not psi,
    c   = enc(pp).

The native finite-formula encoder is the usual homomorphism. Double
negation padding ensures c>3. Every variable name occurring in pp is
strictly below c, by the elementary code-label induction. Hence the
actual private label c is absent from psi. It is also absent from f:
theta retains both endpoint names of each equality atom, all membership
endpoint names, and every old bound name.

Now choose as an ordinary comparison-theory axiom the named K core

    KCore(1,3,c, not not f).

The private label c in this COMPARISON axiom is deliberately chosen from
the encoded INTERPRETED matrix, not from the original matrix. That is
permitted in ordinary K: the private container variable can be any fresh
name. The comparison theory has such an instance for every ordinary
matrix f, and double-negation cancellation plus the usual named/de
Bruijn environment proof recovers every ordinary K schema instance.

Because the outer K template uses only membership, implication,
negation, quantifiers, and matrix insertions, it commutes literally with
theta:

    theta(KCore(1,3,c,not not f))
      = KCore(1,3,c,not not psi).

The interpreted matrix on the right has the actual native code c.
Therefore its native encoding is exactly

    kcore(1,3,c,c),

which is projected from the enabled source bundle with original
parameters a=1,b=3,c. There is no independently selected output code,
re-encoded arbitrary decoder value, or hidden replacement of the private
label. The potential mismatch between a matrix's old code and the code
of its equality translation has been removed by choosing the comparison
instance's private name AFTER interpreting its matrix.

The same literal commuting statement holds for the conditional root:

    Imp(matrix, Ex_c(And(Rel(3,c), closure))).

Thus the conditional two-marker calibration can be used without another
logical change.

## 3. Finite-refutation completeness

Take a finite contradiction in ordinary K+IR. Its matrices have finitely
many free variables, so choose the canonical named representatives f
above and the corresponding comparison instances. The ordinary complete
first-order calculus derives the original finite K assumptions from
these selected instances by matrix double-negation equivalence,
capture-free naming, and universal closure. This is the same finite
ordinary/named reduction used in the pinned KDecodeCore proof, with a
different fresh private-name selection algorithm.

Translate that finite logical proof by theta. Section 1 supplies all
translated logical axioms. Section 2 supplies every translated K axiom
from an actual numerical bundle. The translated IR is

    All_0(F -> F),

a generalized identity, because genuine bottom translates to F and
membership is preserved. The translated conclusion is F. Hence an
ordinary finite K+IR refutation gives a numerical refutation in the
restricted-helper calculus.

Combine this with the pinned K+IR-to-ZFC finite-refutation comparison,
or with the new conditional K interpretation, to obtain

    not Con(ZFC) -> numerical derivability of F.

The logical interpretation is effective on finite proof trees. Every
fresh auxiliary uses a maximum plus one; every matrix code is a concrete
finite-formula encoding; every parameter choice is explicit. Its
formalization in ZFC does not rely on merely external standard-formula
semantics or the strength of Rocq's metatheory.

## 4. Soundness

In genuine first-order equality semantics, every H_kappa is valid:

- If a!=b as names, the assumed condition makes the bound name fresh in
  the atomic equality formula, so it is ordinary vacuity.
- If a=b as names, Eq(a,a) and its universal closure are equality
  theorems, regardless of the binder's label.

The original full-equality calculus therefore proves each new helper.
All K, membership-vacuity, and logical rows are unchanged. The original
relative-falsity and code-zero soundness proof consequently applies, and
the original ZFC interpretation supplies the upper consistency
direction. In the conditional case use the calibrated conditional upper
interpretation as appropriate for its active-role choice.

Together with Section 3 this proves the claimed numerical
equiconsistency.

## 5. What this does not justify

Deleting the equality helper and replacing it only by primitive
symmetry is a different proposal. Source 116's H_sym also retained
positive canonical V, which supplied the equality helper at the actual
equality-code binder. Its Eq-to-E and interpreted rho1 bootstrap must not
be cited as if primitive symmetry alone supplied that missing premise.

The argument here retains an actual H_kappa family. It establishes no
primitive-symmetry-only theorem, no derivation of full primitive equality
vacuity from the restricted family, and no numerical state reduction
without a separately identified source and runtime.
