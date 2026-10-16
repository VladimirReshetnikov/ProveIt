`QuotientReplacement.lean` proves functional Replacement in the actual
bisimulation quotient of a `ProfileModel.ModelsCPGIC` model. The theorem
`quotient_replacement` has exactly the semantic shape of `ZFAxioms.repl`:
for every actual source `Form` and quotient parameter valuation, a functional
formula relation has its image on every quotient set. Functionality uses
actual quotient equality; the relation need not be total. The theorem
`quotient_repl_form` proves the repository's actual `Repl_form` under every
quotient valuation.

The collection resource is the literal equality-free matrix

```text
Mem(0,2) ∧ rename σ (QuotientModel.translate phi)
σ(0) = 1
σ(1) = 0
σ(k+2) = k+3
```

The matrix uses input 0, output 1, domain 2 and later parameter slots, under
the parameter environment `a :: env`. The source relation follows the
repository's `relOf` convention, with output 0 and input 1. Its checked
satisfaction is therefore

```text
mem x a ∧ RelSat mem (y :: x :: env) phi
```

The renaming handles the argument swap and inserted domain parameter without
capturing any binder. Even formulas with logical equality give equality-free
matrices, because the quotient translation replaces equality by bisimilarity.
`replacement_instance` obtains exactly this formula-indexed GIC instance.
It assumes no collection scheme for arbitrary semantic relations.

The predicate is invariant under bisimilarity in both arguments by the
existing `relSat_congr`. The semantic helper `replacement_of_instance` then
constructs the interpreted image. At this intermediate step, functionality
only on interpreted members of the chosen domain suffices. In the actual
quotient theorem, the repository's global `Functional` hypothesis supplies
that condition through `mk_eq_iff`.

An arbitrary quotient valuation is lifted with the stable
`QuotientSeparation.liftEnv` API. `quotient_relOf` checks satisfaction under
that original valuation, and existential quotient inputs are returned to raw
representatives with `Quotient.exists_rep`. Thus the image theorem covers all
quotient parameters and elements. Representative selection is metatheoretic
Lean choice, rather than an object-level Choice axiom. Importing the
Separation module reuses this environment API; the Replacement proof does
not assume or invoke a Separation axiom.

The proof follows the image construction in the attributed upstream
`ZF/m254/coq/settheory/S_ax.v:rep_core` at
`297ab8df7e5de329605c3875b4934643b371a5e3`, using the existing equality-free
profile resources. No Coq proof is imported or built. The generic theorem
requires only the actual CP/GIC model and an explicit raw witness; it adds
no raw Extensionality, profile-congruence, irreflexivity or totality premise.
The existing `Code254GIC.modelsCPGIC_of_encBundle` adapter composes with it
under that adapter's stated irreflexivity and valuation hypotheses.

The source passed its first explicit Lean 4.32.0 build in 0.362 seconds.
All seven theorem axiom audits and three caller examples passed in
0.321 seconds. The equality-free syntax theorem has no axioms; the matrix
satisfaction and instance theorems use only `propext`; the other audited
results use at most `propext`, `Classical.choice` and `Quot.sound`.
There were no warnings, failed builds, admissions, custom axioms or
`native_decide`. The three callers check the actual `ZFAxioms.repl` field
type, sealed `Repl_form` satisfaction and composition from encoded-bundle
models. They do not supply the other ZF axioms.

This was a scoped check using the parent's source-verified 64-module cache;
no full dependency or expensive bootstrap rebuild was run. Complete
commands, compiler version, source/cache identities, axiom output and caller
source are retained in `results/quotient-replacement-verification.json` and
`/tmp/zfc-quotient-replacement-nsncunm_`.

The complete quotient ZF interpretation, the usual Infinity comparison,
Foundation/Choice consistency interpretations, encoded/decoded bundle model
comparison, and linking the abstract enumerator to register and binary
execution remain separate obligations.
No machine or state bound changes here.
