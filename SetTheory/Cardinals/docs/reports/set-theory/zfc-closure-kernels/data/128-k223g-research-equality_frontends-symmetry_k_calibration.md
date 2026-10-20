# A smaller logical basis for the present K family

## Exact candidate calculus

Use the literal current constructors `I=4P`, `R=4P+1`, `Q=4P+2`,
`Eq=4P+3`, falsehood `F=1`, truth seed `0`, and the current K224
fused bundle. Keep rho1–rho6, rho8, full gated membership vacuity,
the canonical helper

    H(a,b) = Eq(a,b) -> Q_(R(a,b)) Eq(a,b),

modus ponens, and theorem generalization. Replace just

    rho7(a,b,c) = Eq(c,a) -> (Eq(c,b) -> Eq(a,b))

by

    Sym(a,b) = Eq(a,b) -> Eq(b,a).

The six ordered choices of two distinct *parameter roles* among a,b,c
all enumerate the same full Sym family, including coincident numerical
values. A chosen source must emit the row without a new freshness gate.
This change has a proved numerical consistency calibration, conditional
only on the same upstream finite-refutation comparison already used for
K224. It does not make the two theories prove exactly the same primitive
Eq formulas.

## Proof of the calibration

The logical ingredient is already present in the pinned Source116
`general_kappa_equality_helper.md`: the membership-defined equality
interpretation works with either rho7 or primitive symmetry, provided
the H_kappa family is retained and kappa(a,b) avoids a,b off the diagonal.
Here R(a,b)>max(a,b), so the condition is satisfied even on the diagonal.

For a,b let k=EqCode(a,b)>a,b and define E(a,b) as the conjunction
of the two universally quantified bidirectional membership-profile
conditions, using k as their bound label. The Source116 argument provides:

1. Membership-only fresh vacuity, by structural induction.
2. Specialization of quantifier-free membership matrices, using Sym,
   rho3/rho5, rho1, rho2, rho6, and membership vacuity. Neither arbitrary
   substitution nor equality vacuity is assumed.
3. Transport between any two safe bound labels, proved through a fresh
   intermediate label; no unproved alpha-conversion principle is used.
4. Full E-vacuity, E-congruence in both membership positions, and the
   ternary E version of rho7, for all coincident label cases.
5. Eq(a,b)->E(a,b), using H(a,b), Sym, and the two congruence rows.
   The diagonal case can instead use the direct theorem E(a,a).
6. Ex_a E(a,b) from rho1 and existential monotonicity.

Classical tautologies used in that argument are derivable from the
unchanged rho8/rho6 bridge. The old positive-canonical-V route to classicality is
unnecessary here. All GEN applications are to closed derivations.

Consequently the complete ordinary equality calculus translates into
this new numerical calculus under theta: preserve membership,
implication, and every quantifier binder; send genuine bottom to F;
send ordinary Eq(a,b) to E(a,b). The native falsehood R(0,0) is fixed.

The K-specific coupling is exactly the argument in K224's
`k_equality_helper_extension.md`, Sections 2–3. For a genuine named
matrix f, choose psi=theta(f), pad by double negation, and choose the
comparison instance's private name to be

    c = enc(not not psi).

This actual integer is larger than every occurring label and is fresh
in both the translated and original matrices. The K template contains
only membership, implication, negative conjunction, quantifiers, and
matrix holes. It therefore commutes literally with theta. The translated
comparison instance is precisely the source's available K core at
input 1, output 3, private/matrix code c, followed if needed by the
already certified fusion equivalence. No independent private-label
choice or recoding of an arbitrary decoder value is made.

Thus a finite ordinary K+IR refutation gives a finite new-calculus
refutation of F. The interpretation of ordinary IR translates to the
generalized identity All_0(F->F). The pinned K-to-ZFC finite-refutation
comparison gives the lower consistency reduction.

For the upper reduction, every new axiom is true in the ordinary K+IR
interpretation with genuine equality. More strongly, the old restricted-
helper calculus proves primitive Sym: its existing rho1/rho2/rho6/rho7
and diagonal H_kappa proof first obtains Eq(x,x), then symmetry. Hence
any refutation in the new calculus is also one in the old calculus.
Together these give equality of their refutation predicates, and
therefore equivalence to ZFC inconsistency.

All transformations are effective on finite syntax. This supplies an
ordinary argument formalizable in ZFC; it is not a new compiled Rocq
or Lean endpoint for any changed transition table.

## Literal emitter word

The upstream macro names from the current exact emitter checker are:

    PushA=166, PushB=121, PushC=168, Imp=119, Eq=182.

The postfix constructor words are:

    rho7: [168,166,182,168,121,182,166,121,182,119,119]
    Sym(a,b): [166,121,182,121,166,182,119]

The shorter row saves four macro invocations before sharing. A machine
state count does not follow from that number: all shared aliases,
source control boundaries, runtime paths, and the blank bootstrap must
be reconstructed and checked. The source-reduction agent is measuring
the six ordered parameter choices.

## Precise separation from an unsupported proposal

Deleting H_kappa while keeping only Sym is a different system. The
Eq-to-E bridge above actually uses H_kappa. This note supplies no
calibration for that further deletion.

## Primary local provenance

- K224 construction archive in ProveIt commit
  `49ee7cfdc8e0364c6db3614675d141d66f9350ed`.
- `portable/theory/source116/proofs/general_kappa_equality_helper.md`.
- `portable/theory/source116/audit/mathematical_audit.md`.
- `portable/theory/source116/proofs/indiscernibility_certificates.py`:
  its `SYM` leaf is already primitive symmetry, and the E law proofs
  do not use rho7 or primitive equality vacuity.
- `portable/theory/k_equality_helper_extension.md`.
- `portable/theory/fused_k_theory.md`.
- Glazer k230-rocq `Codes230.v`, `CD230.v`, and `KUpperConsistency.v`,
  pinned upstream at `3142e4dd980f0be12f4abb636c4ae2528afc17eb`.
