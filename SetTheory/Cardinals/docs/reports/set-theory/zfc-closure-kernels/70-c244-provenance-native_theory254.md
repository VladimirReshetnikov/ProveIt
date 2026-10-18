# An explicit first-order theory for the structured program

`NativeTheory254.lean` defines a literal sentence theory `NativeAx`:

```text
sealF ProfileModel.containerForm
sealF (ProfileSyntax.gicForm phi)    for every actual native Form phi
sealF (∀x (x∈x → Bottom)).
```

There is no Extensionality, Foundation, Choice or extra model-existence
axiom. Native equality is the ordinary logical equality of `Form`; the
GIC schema ranges over every finite formula, not only equality-free ones.
`sealF` universally closes all matrix parameters. `sentences_NativeAx`
checks this sentence presentation, and `models_NativeAx` proves its exact
content at a supplied valuation: raw CP containers, full actual-formula
GIC, and raw irreflexivity. Its proof uses the existing `extract` and
`closeN_valid` lemmas, with no unexpressed semantic relation schema.

The new main theorem is

```text
Code254.C254 Code254.F ↔ BProv NativeAx [] Form.fBot.
```

For the forward implication, every native theory model supplies the
numerical soundness model class through `NativeDecoded254`. Numerical
falsity therefore contradicts every supplied native model/valuation.
The repository's `completeness_inf` for sentence theories then gives an
actual finite `BProv` refutation. This does not use an impossible
no-model premise over empty domains: the completeness API explicitly
supplies `v : Nat → D` with its model.

For the reverse, suppose the native theory has a finite refutation.
Every nonempty irreflexive `ModelsEncodable` model supplies raw CP and
full native GIC through the existing concrete matrix adapters, so it
satisfies every closed native axiom. Ordinary first-order soundness
makes its alleged refutation impossible. The actual
`Code254.c254_complete` theorem, with its explicit valuation argument,
therefore supplies numerical falsity. This proves refutation equivalence
using the real numerical and first-order calculi; no new abstract
completeness assumption is introduced.

Composing the proved `L2.program_halts_iff` gives

```text
RMDag.IterHalts Dag254.dag254 (upd (fun _ => 0) 0 2)
  ↔ BProv NativeAx [] Form.fBot.
```

The initial vector has `nextproof=2` and every other register zero.
`native_consistency_iff_program_nonhalting` is its exact contrapositive.
`IterHalts` is finite repeated-root execution ending in the genuine halt
exit; it does not count divergence or a stuck instruction as halting.
The theorem concerns the actual219-node structured DAG. It neither
identifies that DAG with the distinct literal `Prog254` tree nor closes
the binary-tape simulation.

This is an exact native theory interface for the original C/G/IR source
calculus. It does not supply the Foundation/Choice consistency transports,
calibrate `NativeAx` with ZFC or ZF0, build a new smaller machine, or
assert a new nonhalting result. The proof uses semantic completeness to
obtain finite proofs; it does not implement a computable arithmetic
proof-code transformer. The raw quotient and its separate IR obstruction
are unnecessary for this numerical/native-theory comparison.

The102-line source compiles on its first check with the explicit pinned
Lean4.32.0 compiler in0.23seconds. Eight theorem axiom audits and three
callers pass first check in0.14seconds. Only `propext`, `Classical.choice`
and `Quot.sound` occur; `sat_irForm` is axiom-free. The callers check that
native Eq(1,2) GIC is an actual closed theory axiom, that a supplied native
model excludes structured-program halting, and that a native refutation
produces both numerical falsity and actual structured-program halting.
Commands, exact caller source and audited dependency sets are in
`results/native-theory254-verification.json`. No Coq or full bootstrap
rebuild was performed.

