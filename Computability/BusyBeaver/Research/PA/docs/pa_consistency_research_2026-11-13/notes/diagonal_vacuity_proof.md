# A formula code supplies its own fresh binder

## The reduced gate

Use PA196's numeric constructors I, M, U and E, including its transposed
universal code U(a,B)=4p(B,a)+2, its code-0 truth convention, and its
designated contradiction 1=M(0,0). Put N(B)=I(B,1).

Retain the six logical heads, restricted propositional head, modus ponens,
and generalization. In the guarded gate replace the equality-vacuity
clause

    Delta_c(a,b) = E(a,b) → U(c,E(a,b))

by

    Gamma(B) = B → U(B,B),

where B is any one of the three independent numerical parameters a,b,c.
For example, with B=a, the new gate is

    F'(a,b,c) = N(Gamma(a) → (V(a,b,c) → Q(a,b,c))),
    V(a,b,c)  = M(a,b) → U(c,M(a,b)),

with the original Q and the original guard c≠a,b. Swapping the first two
antecedents Gamma and V gives an equally valid variant.

The existing propositional extraction proofs give both Gamma(B) and the
old membership-only gate N(V→Q). Every Gamma(B) is available despite the
guard. For the displayed B=a choice, instantiate the gate at
(a,b,c)=(B,B,B+1). For B=c, take (a,b,c)=(B+1,B+1,B), and for B=b one may
use the first assignment with the parameter roles interchanged. Thus the
following diagonal vacuity schema is derived uniformly:

    B → U(B,B)                                            (DV)

Every variable label occurring in decode(B) is below B. Consequently the
variable x_B does not occur in its own coded formula, and (DV) is sound.
This is also valid at B=0, whose decoded formula is truth.

An AX implementation uses the seven macro tokens

    copyB, copyB, copyB, cons, incT, incT, cons.

The first copy preserves the preceding stack item. After the second and
third copies, `cons; incT; incT` produces U(B,B); the final cons produces
I(B,U(B,B)). This replaces 17 tokens by seven, reducing the AX word from
201 to 191 tokens while retaining all nine pushed items, their order,
the final guard and the command-selection protocol. No new macro is needed.

## The logical interfaces that suffice

The upstream PA-refutation compiler uses primitive equality through:

(R) Both directions of membership rewriting under E(a,b), in either
    argument of membership.

(N) E(a,b) → R_z(a,b) whenever z≠a,b, where

    R_z(a,b) =
      U(z, M(a,z)↔M(b,z)) ∧ U(z, M(z,a)↔M(z,b)).

(W) Existence of a witness for this defined equality.

The construction below recovers these interfaces without assuming
primitive equality symmetry, transitivity, or unrestricted equality
vacuity. The retained heads still derive all propositional proof operations,
including explosion from code 1, as in PA196/Logic/Deduction.lean; treating
code 1 as a contradiction here is a derived rule, not an additional axiom.

## Membership-only vacuity

The old gate N(V→Q) remains derivable, so it supplies unrestricted membership
vacuity and pointed separation. The existing finite proofs of
`negationVacuity`, `implicationVacuity`, `conjunctionVacuity`, and
`universalVacuity` therefore remain available. The applications below need
only quantifier-free membership matrices, followed by at most one universal
quantifier whose label is distinct from the new binder. Their vacuity
proofs are obtained by following the displayed constructors, starting from
freshness at each membership atom. None uses primitive equality vacuity.

## Reverse rewriting: negate the desired conclusion

First consider one of the three upstream membership-property families:

    chi_1(d,t)=M(t,d),
    chi_2(d,t)=M(d,t),
    chi_diag(d,t)=M(t,t).

Write p=chi(d,a) and q=chi(d,b). Assume a≠b and, for a non-diagonal
family, a≠d. Define

    C   := E(a,b) → (q → p),
    phi := N(C),
    c   := the numeric code phi.

Here phi and c are the same natural number, viewed respectively as a
formula code and as the variable label of the separator. Cantor coding
gives c>C, and C is greater than every label occurring in E(a,b), p and q.
Thus c≠a,b, and it is also distinct from d when d occurs. There is no
collision branch and no padding search.

Use pointed separation with the two object labels both equal to a and
property code c. Abbreviate

    P := phi → M(c,a),
    S := U(a, (M(a,a)→P) ∧ (M(c,a)→phi)),
    Q := U(c, S→N(P)).

The retained old gate gives N(Q). We will derive phi→Q, contradicting phi.

### Extract only the negative membership consequence of the property

Propositional logic gives

    phi → E(a,b),       phi → q,       phi → N(p).        (1)

From S, project its second conjunct under U(a). Use the last implication
of (1) to weaken its consequent. This gives

    S → U(a, M(c,a)→N(p)).                              (2)

The upstream `negativeSpecialization` lemma now applies unchanged:

* the direct primitive rewrite supplies E(b,a)→(q→p);
* q has vacuity at a because it is a membership atom with the indicated
  freshness conditions;
* M(c,b) has vacuity at a because c≠a,b;
* the existential mirrored equality witness is one of the retained heads.

Consequently (2) gives

    S → (M(c,b)→N(q)).                                 (3)

This is the crucial separation of concerns: the equality atom inside
phi is never transported or specialized. It has been discarded by the
propositional implication phi→N(p) before the membership specialization.

### Close the separation argument using diagonal vacuity

Under assumptions phi,S,P, implication P gives M(c,a). From phi we have
E(a,b) by (1), so the direct primitive rewrite in the second membership
argument gives M(c,b). Equation (3) then gives N(q), whereas (1) gives q.
Discharge P and S. This is a finite derivation of

    phi → (S→N(P)).                                    (4)

The derived schema (DV), instantiated at the formula code phi=c, is
exactly

    phi → U(c,phi).                                    (5)

Generalize the closed derivation (4) at c and apply the retained universal
distribution head to (5). The result is

    phi → U(c,S→N(P)) = phi → Q.

Together with N(Q), this gives N(phi)=N(N(C)); double-negation elimination
gives C. This proves the reverse membership rewrite for the selected family.

The upstream collision cases extend it to all labels. If a=b, the desired
rewrite follows by identity and weakening. If a=d in a non-diagonal family,
one direct membership rewrite first reaches the diagonal family, and the
new diagonal argument finishes the proof, exactly as in the existing
`reverseRight` and `reverseLeft` constructions. Hence (R) holds without any
remaining side condition.

Every step is a finite syntactic proof operation. The parameter c is
obtained by a fixed composition of numeric constructors. The construction
is primitive recursive and PA can verify the produced proof code.

## Neighborhood equality from one diagonal binder

Let e=E(a,b) and z0=e. This numeric code is strictly greater than a and b.
The instance (DV) at e gives

    E(a,b) → U(z0,E(a,b)).

Using (R), derive both matrices of R_z0(a,b) under the assumption E(a,b).
Generalize each at z0 using the displayed vacuity proof, then conjoin them.
This recovers the upstream neighborhood implication at the particular
fresh binder z0:

    E(a,b) → R_z0(a,b).                                (6)

## Transport that binder to any fresh label

Fix z≠a,b. If z=z0, (6) is already (N). Otherwise let Phi(u) denote either
of the two quantifier-free matrices

    M(a,u)↔M(b,u),        M(u,a)↔M(u,b).

The recovered (R) and propositional reasoning give

    E(z,z0) → (Phi(z0)→Phi(z)).                         (7)

Because z0≠a,b,z, the target Phi(z) has membership-only vacuity at z0.
Apply the retained mirrored witness ∃x_z0 E(z,z0), (7), and the upstream
`specializeWithMirroredEquality` construction. It gives

    U(z0,Phi(z0)) → Phi(z).                            (8)

The sole vacuity premise in that specialization concerns Phi(z), a
quantifier-free membership formula. No primitive equality-vacuity instance
is needed.

The assumption U(z0,Phi(z0)) is also membership-only and is fresh for z.
Its vacuity at z follows from membership vacuity and universalVacuity.
Generalize (8) under that assumption and discharge it to obtain

    U(z0,Phi(z0)) → U(z,Phi(z)).                        (9)

Apply (9) to both neighborhood conjuncts. This yields

    R_z0(a,b) → R_z(a,b).

Together with (6) it proves the exact original interface (N) for every
z≠a,b. This explicit binder transport replaces any appeal to a global
renaming or large-eigenvariable convention.

## Witnesses and calibration to PA

The original head gives ∃x_a E(b,a). Existential monotonicity applied to
(N), followed by the symmetry of the defined membership relation R_z,
gives (W), exactly as in the upstream `neighborhoodWitness` derivation.

All required inputs of the original relational PA compiler are therefore
restored: (R), (N), (W), the six heads, the restricted propositional basis,
membership vacuity, and pointed separation. The transposed formula coding
is unchanged. Substituting the finite proof suppliers above into that
compiler gives a primitive-recursive, PA-verifiable transformation from
PA refutations into derivations in the reduced calculus.

Conversely, interpret M(a,b) as Bit(x_a,x_b), with the first argument the
container, and E(a,b) as actual equality. Gamma(B) is a logical theorem
because x_B is absent from decode(B). The remaining old gate is supplied
by full-PA finite binary comprehension, and all other heads are unchanged.
The syntactic proof translation described in pa_reverse_translation.md
therefore sends every refutation of the reduced calculus to a PA
refutation, with correctness provable in PA.

The two refutation predicates are thus equivalent in PA. A literal
machine implementing the reduced command search, with the usual
PA-formalizable finite source/tape simulations, satisfies

    PA ⊢ (Nonhalt(machine) ↔ Con(PA)).

This is a mathematical proof of the changed calculus. It is separate from
the machine-level transition table, state census, startup and symbolic
simulation certificates, and it is not described as a completed Lean
formalization of the new calculus.

## Further research questions

1. Formalize the short replacement for reverseFromProperty directly in
   the upstream Lean proof language, retaining its explicit contexts.
2. Compare Gamma at each of the three AX parameters and both orders of
   Gamma and membership vacuity in the gate. They have identical logic
   but can have different compressed source trees.
3. Determine how much of the unrestricted membership-vacuity schema is
   essential. Removing it is not justified by this argument: its use in
   negativeSpecialization and neighborhood binder transport is explicit.
4. Investigate the more general method of taking the separator's property
   to be the negation of the desired implication, so its own diagonal
   vacuity is exactly the premise needed when closing the proof.
