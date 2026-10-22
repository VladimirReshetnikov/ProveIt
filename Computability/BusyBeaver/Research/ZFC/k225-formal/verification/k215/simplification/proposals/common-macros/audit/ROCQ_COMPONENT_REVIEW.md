# Independent source review of the Rocq macro component

Status: **PASS**, for the exact source hashes in
`macro_component_review.json`. This review parses and reads the sources; it
does not itself execute a proof compiler. The component's compiler and
recursive-checker evidence is a separate artifact.

## Generic theorem

`LocalProgram.Closed p q ok` permits either identical child edges within the
closed region or a proved whole-node run transport contract. `run_transfer`
is proved by induction on the actual repository `K230.RM.run` relation. It
preserves all four exit constructors (`XNormal`, `XBreak`, `XContinue`, `XHalt`)
and the exact final natural-valued register function.

The key looping constructor is handled explicitly: `run_node_cdr_continue1`
transfers the car and cdr runs with the child closure facts, then transfers the
recursive run at the same node using its original membership fact `Hi`. The
whole-node contract branch reconstructs the original run before applying the
contract; it does not assume the desired theorem recursively.

The finite checker covers all nodes where `ok` is true, because
`check_closed_sound` separately requires and uses the bound
`ok n = true -> n < bound`. It checks equality of the complete pair of edges
and membership of both children. The fact that inactive nodes pass its Boolean
test therefore leaves no unchecked active node.

## Exact program binding

The canonical macro program has precisely the 89 rows found by the independent
source census. Its rows equal both the maintained literal `DagPerm` and
`DagDom` rows on those indices, and all node children remain inside the set.

The 215 and 217 bindings each invoke `check_closed_sound` with bound 467 and
prove the finite equality by `vm_compute; reflexivity`. They prove both
directions separately. The optional `macro_215_217_iff` composes those local
directions through the canonical program.

The original combined binding module would have brought the entire 217 table
into the 215 adapter's import closure. Following review, the author split
`Macro215Binding` and `Macro217Binding`. The final 215 contract closure contains
ten project modules and no `K217F` module; the cross-candidate theorem lives in
the separate optional `MacroBindings` module.

## Arithmetic contracts

`MacroLibrary.v` is exactly the old `ProgLibPerm.v` under these three textual
substitutions:

1. `From K215F Require Import DagPerm.` becomes the canonical-program import.
2. `dagPerm` becomes `macro_prog`.
3. `dag_nodes` becomes `macro_nodes`.

No arithmetic proof was changed in that retargeting. All 58 literal-node lemma
statements in `Macro215Contracts.v` match the corresponding maintained
statements after whitespace normalization. The adapter transports their runs
through `sem_lift` while retaining the same final register approximation.
The conjunction-valued `loop463` and existential `l464_neq` are handled
explicitly rather than forced through the simpler adapter pattern.

## Boundaries that must remain explicit

- The component uses the common `MacroLibrary.St` record. That is not nominally
  the old separately declared `ProgLibPerm.St`, so textual signature equality
  is not yet an existing-API compatibility audit. A production refactor must
  preserve or adapt the register utilities and then check `L2RootPerm`.
- The canonical program has root 115 as a library artifact. Candidate root 0
  is outside the macro footprint. No whole-program Dom/Perm equivalence is
  claimed; the actual dispatch behavior intentionally differs.
- The eight component files total 1,300 lines and 61,524 bytes. The maintained
  single `ProgLibPerm` has 780 lines and 37,951 bytes; the two old libraries
  have 1,561 lines and 75,953 bytes. These figures establish a checked reuse
  component, not an achieved reduction of the entire 215 endpoint. Avoid
  subtracting only a retired candidate file while ignoring shared code.
- The full endpoint, producer synchronization and old client integration remain
  separate work. A generic parameterized macro API or functor can avoid
  copying the 58 thin theorem adapters for every additional candidate.

## Reproduction

```
python3 audit_macro_component.py /path/to/ProveIt /path/to/rocq_component/src \
  > macro_component_review.json
```

Keep `audit_macro_footprint.py` alongside the component audit script; the latter
reuses its literal-table parser and nested-comment handling. Both scripts are
read-only and use only the Python standard library.
