# Internal ZF proofs of the fixed Collection template

`CompiledCollection254.collectionProof K` produces an internal ZF proof of the
translated fixed Collection sentence for every internal binary predicate K in
every IΣ1 model. K may retain arbitrary free parameters. Every source axiom
callback is discharged; there is no remaining Separation, Replacement,
congruence, or shift-invariance premise.

The source is the checked ordinary `CollectionTemplate254.collection_provable`
derivation. Its theory contains lifted pure ZF, equality for the expanded
language, and exactly three relation-dependent sentences: witness-rank
Separation, globally total least-rank Replacement, and output Separation.
`OpenSchemaTemplates` supplies those three schema proofs with their ordinary
parameters universally closed. Pure equality axioms are literal lifted ZF
axioms; the only added relation axiom is binary predicate congruence, supplied
by `SetCongruence.congruenceProof₂` for arbitrary internal K.

The buffered compiler receives this complete callback at every finite shifted
predicate family. It translates one fixed ordinary proof while preserving K's
additional free parameters. The final `collectionProof_isProof` theorem exposes
the resulting proof code and the actual ZF proof relation. The construction
uses Lean proof carriers and a fixed ordinary derivation; it does not yet
provide a represented arithmetic proof-code selector or identify the machine's
decoded G formula. Those are separate interfaces.

The first complete check is run3: five ordered axiom probes, eight callers,
standard axioms only, and zero warnings. Source compilation took 2.417 seconds
and the caller audit 2.040 seconds. The audit includes shifted predicates and
a predicate containing an arbitrary free label. The guard combines the three
exact predecessor records and checks matching shared providers: 34 project
modules, ten external source/object boundaries, and Init/Std/Lean/Omega. All
106 inputs and the fresh object pass before/after checks. No dependency was
rebuilt or downloaded, and no resource option was increased.

Both earlier failed source attempts are preserved. They exposed normalization
of the five finite pure equality axioms under the language map. Explicit
relation-symbol, vector-tail and singleton normalization closed those goals;
the callbacks, hypotheses and endpoint did not change. The maintained-default
preparation is separately recorded as `PREPARED_NOT_BUILT`.

With the pinned existing dependency build and matching recorded objects:

```sh
python3 Logic/Interpretability/ZFCinPA/check_compiled_collection254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/Proofs \
  --output /outside/new-empty-directory
```

The checker selects maintained predecessor evidence by default and accepts
explicit evidence/cache/library paths. `--prepare-only` validates the setup
without compiling a proof; it may query the compiler version. The portable
checker is byte-identical to the successful executed checker.
