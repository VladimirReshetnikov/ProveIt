# First-order Separation in the CP/GIC quotient

`QuotientSeparation.lean` proves the full Separation schema for the actual
bisimulation quotient of a `ProfileModel.ModelsCPGIC` model. Its theorem
`quotient_separation` has exactly the semantic shape of `ZFAxioms.sep`:
for every `Form`, quotient parameter valuation and quotient object a,
there is b whose quotient members are precisely the members of a that
satisfy the formula. `quotient_sep_form` proves satisfaction of the
repository's actual `Sep_form` for every formula and valuation.

The module is generic over CP/GIC models. It does not assume raw
Extensionality, profile congruence, irreflexivity or collection for
arbitrary semantic relations. A supplied raw witness makes the underlying
domain nonempty. The earlier `Code254GIC.modelsCPGIC_of_encBundle` supplies
this model interface from literal encoded-bundle models under its stated
IR and valuation hypotheses, so the results compose.

## The exact collection matrix

For a requested quotient formula phi, use the literal equality-free matrix

```text
Mem(0,2) ∧ Same(1,0) ∧ rename σ (QuotientModel.translate phi)
σ(0) = 0
σ(k+1) = k+3
```

Its input and output remain at slots 0 and 1; slot 2 holds the domain a,
and later slots hold phi's parameters. The source parameter environment is
`a :: env`. `sat_separationChoiceForm` checks its actual `MatrixRelation`:

```text
mem x a ∧ Same mem y x ∧ RelSat mem (x :: env) phi
```

This is exactly the existing `ProfileAxioms.SeparationChoice` predicate.
The matrix is equality-free even when phi uses logical equality, because
the checked quotient translation replaces equality by bisimilarity.
`separation_instance` therefore follows from the actual formula-indexed
GIC schema, with no additional representation assumption.

The quotient predicate `RelSat mem (x :: env) phi` is invariant under
bisimilarity by `QuotientModel.relSat_congr`: slot 0 uses the supplied
bisimilarity, and all parameters use reflexivity. The existing semantic
`separation_of_instance` now gives `interpreted_separation` for arbitrary
actual formulas. The witness also retains its `SubD` trace bound, useful
for the later interpreted Power Set construction.

## From interpreted predicates to actual quotient formulas

For an arbitrary quotient valuation, `liftEnv` chooses a raw representative
at each index; `mk_liftEnv` proves that each chosen representative maps to
the original value. This is metatheoretic representative choice in Lean,
not an assertion that the quotient satisfies an object-level Choice axiom.

Quotient induction handles the domain object and tested element.
`sat_quotient` and `mk_scons` transfer the interpreted predicate to the
requested actual quotient formula under the original valuation. Thus
`quotient_separation` quantifies over all quotient parameters, rather than
only the images of a preselected raw environment. `ZF.Zf.bridge_Sep`
then yields `quotient_sep_form` without changing the schema or syntax.

The trace argument follows upstream `S_ax.v:sep_core` at
`297ab8df7e5de329605c3875b4934643b371a5e3`, using the repository's existing
equality-free profile resources. It does not import the Coq proof or claim
a complete Lean port of the upstream set-theory interpretation.

## Verification and scope

The module compiles with the explicit pinned Lean 4.32.0 compiler in
0.35 seconds. All seven theorem axiom audits pass. The equality-free syntax
proof uses no axioms; the remaining dependencies are at most `propext`,
`Classical.choice` and `Quot.sound`. No admissions or custom axioms occur.
Three callers check:

- The theorem can be assigned to the actual `ZFAxioms.sep` field while the
  other fields are supplied separately; this is a type compatibility
  check, not a construction of all ZF axioms.
- Every universally closed `sealF (Sep_form phi)` holds.
- The encoded-bundle model adapter composes with the quotient Separation
  theorem.

Commands and results are recorded in
`results/quotient-separation-verification.json`. The other quotient ZF
axioms, the singleton-closed versus usual Infinity comparison, the
opposite ZFC-to-source interpretation, numerical enumeration and binary
execution remain separate. No machine or state bound changes here.

The subsequent [Power Set](quotient_power.md) and
[Replacement](quotient_replacement.md) modules now discharge those actual
quotient axioms using literal formula-indexed instances. The other remaining
interpretation and machine obligations are unchanged by these results.
