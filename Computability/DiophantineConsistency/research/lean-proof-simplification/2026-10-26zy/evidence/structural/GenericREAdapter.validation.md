# Generic RE adapter validation

**Result: checked in Lean 4.32.0, exit status 0.**

`GenericREAdapter.lean` independently validates the `Nat.rfind` / `REPred` proof body proposed in the split candidate's `DiophantineConsistency/Computability.lean`. It abstracts the literal halting test as `f : ℕ → ℕ`, its primitive-recursive proof as `hf : Nat.Primrec f`, and its semantic predicate as `r : ℕ → Prop` with the hypothesis

```lean
hr : ∀ n, (∃ t, f t = 1) ↔ r n
```

This matches the production predicate's constant dependence on its input. The original production source defines `refutationInputs := fun _ => C222 F`; its equivalence theorem supplies exactly the propositional binding abstracted by `hr`.

The check validates the construction of the primitive-recursive Boolean test, the `Partrec.rfind` search, the recursively enumerable domain, and the final `REPred.of_eq` transport. It does not validate `DirectEnumerator.program`, its extensional equality with `haltingTest`, the new scalar-to-vector primitive-recursive wrapper, or the entire proposed import graph.

The complete axiom report is:

```text
'GenericREAdapter.search_predicate_re' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` and no newly introduced axiom.

## Environment and dependency scope

The exact Mathlib source revision was `81a5d257c8e410db227a6665ed08f64fea08e997`. The pre-existing package cache lacked seven modules in the dependency closure of `Mathlib.Computability.RE`. Only these modules were compiled, all successfully, into the current workspace's `mathlib_extra` directory:

1. `Mathlib.Computability.Primrec.Basic`
2. `Mathlib.Computability.Primrec.List`
3. `Mathlib.Data.Nat.PSub`
4. `Mathlib.Data.PFun`
5. `Mathlib.Computability.Partrec`
6. `Mathlib.Computability.PartrecCode`
7. `Mathlib.Computability.RE`

Existing cached modules were accessed through a read-only symlink overlay. Every newly produced `.olean`, `.olean.private`, `.olean.server`, and `.ir` is a regular file under the current workspace; the corresponding prior-cache `.olean` paths remain absent. No prior workspace source or build output was modified. The dependency compilation and final adapter check took 22.97 seconds in this environment, which is an execution record, not a performance comparison.

`generic_re_build_manifest.json` records the seven exit codes, module timings, adapter exit code, prototype hash, and output isolation checks. `check_re_adapter.py` records the environment-specific dependency-check command. Do not bundle the `mathlib_extra` symlink overlay as a portable deliverable.

## Reproduction in a complete matching checkout

With Lean 4.32.0 and Mathlib at the revision above, and the required Mathlib cache populated:

```sh
lake env lean GenericREAdapter.lean
```

The standalone proof and its axiom report are the portable validation artifacts. Production acceptance still requires rebuilding the proposed split source modules and their downstream clients in the pinned ProveIt checkout.
