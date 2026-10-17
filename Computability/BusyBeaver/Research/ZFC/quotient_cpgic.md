# CP and native-formula GIC in the bisimulation quotient

`QuotientCPGIC.lean` transfers actual equality-free `ProfileModel.ModelsCPGIC`
to CP and GIC for **every native `SetTheory.Form`** in the existing quotient.
The only other input is an explicit raw inhabitant. The source does not
assume collection for arbitrary semantic predicates, raw Extensionality,
Foundation, Infinity, object-level Choice or irreflexivity.

The essential new instance is the literal equality-free matrix

```text
mem x a ∧ mem y a ∧ Same y x ∧ RelSat (x :: env) phi.
```

`strongTraceForm` places raw input/output at slots0/1 and `a` at2. The
capture-correct `separationRename` moves each old formula parameter past
those extra slots. The remaining formula is `QuotientModel.translate phi`,
so native equality is represented by the existing bisimilarity formula.
`strongTrace_instance` requests exactly that actual matrix from raw GIC.
Its global support clause makes every raw output a raw member of `a`.
Its cover clause can still choose output equal to input. Bisimilarity
invariance of interpreted satisfaction then gives a trace `r` with

```text
r ⊆raw a
Member z r ↔ Member z a ∧ RelSat (z :: env) phi.
```

The output guard is essential: the older `separationChoiceForm` only
supplies `SubD`, which does not justify applying a raw power bound inside
the same container.

Specializing to `phi = Mem(0,1)` and the constant environment at `z`
shows every interpreted subset of `a` is bisimilar to a literal raw subset
of `a`. Interpreted Extensionality identifies the two representatives.
Given the original raw CP container `v`, first replace an interpreted
member by its raw member witness in `v`. Raw transitivity then proves
quotient transitivity. For the power-bound clause, the strengthened trace
places a representative of each quotient subset inside that raw witness;
the original raw CP bound therefore contains a representative of every
quotient subset. The very same `v` supplies `quotient_containers`.
This argument uses no rank hierarchy or larger-container iteration.

Full native-formula GIC takes the actual raw instance `translate phi`
and lifts the supplied quotient parameter valuation to representatives.
`relSat_congr` transports the input and output along bisimilarity. Global
support yields an input somewhere in the universe, with no unsupported
domain restriction. Cover transports a domain member to its raw witness,
uses raw cover, then transports the matrix back. `sat_quotient` relates
those instances to native quotient equality. Thus `quotient_fullGIC` has
no `EqualityFree phi` hypothesis. `quotient_fullCPGIC` combines it with
actual CP; `quotient_modelsCPGIC` is the weaker reusable EF interface.

This closes the twins/native-equality obstruction **after quotienting**.
It does not produce a `Code254.ModelsDecoded` model. In particular,
quotient irreflexivity is still a separate obligation: raw
`∀x, ¬mem x x` does not directly prohibit `Member x x`, which can use a
distinct bisimilar raw representative. No raw-IR-to-quotient-IR theorem or
countermodel is asserted by this module. The additional actual numerical
bundle/zero-alias gates, reverse consistency interpretation and full
literal-machine correspondence remain separate.

The route uses the repository's checked `QuotientModel`,
`QuotientSeparation` and `QuotientPower` interfaces. It is a direct
same-container refinement of the trace construction, independently read
against those definitions. No machine table or state count changes.
The232-line module compiles with the explicit pinned Lean4.32.0 compiler
in0.42seconds. Thirteen theorem axiom audits and three callers pass
in0.30seconds; only `propext`, `Classical.choice` and `Quot.sound` occur.
No admissions or custom axioms occur. Commands, caller source and complete
audit output are in `results/quotient-cpgic-verification.json`. The callers derive an actual singleton from the
native matrix `Eq(1,2)`, an actual empty object from Bottom, and collection
for a quantified native-equality matrix with colliding parameters.
