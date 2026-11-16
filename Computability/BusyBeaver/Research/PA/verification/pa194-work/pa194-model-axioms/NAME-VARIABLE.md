# Guarded variable naming in the full source theory

`fullSource_eVar` proves the `NameFacts.eVar` requirement for the existing adjunctive theory with full parameterized separation, for each model-valued variable index. It assumes a model of the candidate PRA presentation whose arithmetic reduct satisfies IΣ₁. It introduces no source-proof hypothesis. Singleton notation is equivalent to the `insert ... ∅` in the structure field.

The first module reduces naming to guarded translated equality reflexivity using the revised compiler's existential-variable rule. The second obtains guarded reflexivity by specializing a closed translated reflexivity proof and extracting the appropriate domain guard. The third supplies that closed proof from the previously checked full-source reflexivity and packet-independence theorems, including quote/free-variable-bound correspondence.

This is a model-level result. It does not supply the other `NameFacts` fields, a native iPRA theorem, the complete PA-to-source interpretation, or either PA194 halting equivalence direction. These three source modules are rebuilt in one output, while imported dependencies are prebuilt; direct repository-replay objects and source inputs are pinned in `pins.sha256`. The legacy transitive imports in `LEAN_PATH` are not rebuilt by this script.

Run from the repository root:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-name-variable.sh "$PWD" /dev/shm/pa194-name-variable-repo-NEW
```

Every checked theorem's printed axiom dependencies omit `sorryAx`.
