# Combining equality symmetry and the canonical vacuity helper

## New schema

Let e=Eq(a,b), f=Eq(b,a), z=kappa(a,b), and let conjunction have the
literal negative encoding A&B=not(A->not B), with F=1. Replace both
primitive symmetry and the ordinary helper H_kappa=e->All_z e by the
single schema

    J_kappa(a,b) := e -> All_z(e & f).

No rho7 row is needed. The remaining logical rows are rho1–rho6 and
rho8; full membership vacuity, the K bundle, MP and theorem GEN remain.
The old rho7 slot may be removed, or replaced by an emitted truth code0
if the source protocol requires a fixed number of slots. The source and
enumerator interface must state which choice is made.

When kappa avoids a,b off the diagonal, J is valid in ordinary equality
semantics. On the diagonal e and f are the equality theorem Eq(a,a),
so even a colliding binder is harmless. In particular both the current
Rel(a,b) and the new a+b+1 binders qualify.

## Closed finite derivation of symmetry and H

The unchanged rho8/rho6 bridge supplies classical propositional logic. Rho1,
rho2 and closed GEN supply the seriality theorem for every formula A:

    All_z A -> Ex_z A.

Indeed rho1 gives Ex_z Eq(z,z). Generalize the propositional theorem
A->(Eq(z,z)->A), distribute by rho2, and use the standard existential
consequence of rho2 to combine those premises. No equality theorem or
vacuity premise is used.

Put D=e&f. J and D->e give

    D -> All_z D.

Generalize this closed implication at z and distribute:

    All_z D -> All_z All_z D.

Seriality at A=All_z D, followed by rho6(z,D), gives

    All_z All_z D -> Ex_z All_z D -> D.

Thus All_z D->D. Combining with J yields e->D, and hence e->f,
which is primitive symmetry. Separately, quantifier monotonicity applied
to D->e gives J's consequence e->All_z e, the old helper H.

All GEN applications in this proof are to closed theorems. The proof
is uniform in arbitrary labels, including all coincidences, and in the
literal relative-falsity encoding. Freshness is needed only to validate
J in standard equality semantics, not for the displayed derivation.

## Reverse derivation

Given H and primitive symmetry, quantifier monotonicity gives
All_z e->All_z f. H therefore gives both All_z e and All_z f under e.
The rho2 consequence

    All_z e -> (All_z f -> All_z(e&f))

then gives J. Hence these two logical presentations are mutually
interpretable on exactly the same formulas by finite proofs.

The existing Source116 membership-defined equality argument calibrates
H+Sym, and K224's actual matrix/private-code coupling transfers that
logical interpretation to the present K schema. Therefore J with rho7
removed has the same refutation predicate as the calibrated K family.
The logic-side proof is complete; whether this presentation saves machine
states is an independent source/compiler measurement.

## Checked proof data

`combined_helper_certificate.py` builds and independently checks all
proof nodes, validating TAUT by complete truth-table enumeration, every
rho leaf by exact syntax, every MP by exact matching, and every GEN for
closedness. One schematic instance has:

- J -> primitive symmetry: 31 distinct proof nodes;
- J -> H: 8 distinct proof nodes;
- H plus primitive symmetry -> J: 20 distinct proof nodes.

It also checks five literal label assignments, including all-zero
coincidence and large labels. These finite instances are regressions;
the schematic proof above is the uniform argument. No new compiled
Rocq/Lean theorem for a transition table is asserted.
