# Represented set-schema axiom constructors

[`ModelCodedSchemaAxioms`](Lean/ZFCinPA/ModelCodedSchemaAxioms.lean) constructs
actual represented ZF and ZFC Separation/Replacement axiom proofs in every
IΣ1 arithmetic model. The input is an internally well-formed set-language
matrix of external arity one or two satisfying `K.shift = K`. Its code may
be nonstandard; no object set-theory model is assumed.

The recognizer proof supplies internal witnesses `m = 0`, `b = body.val`
and core `K.val`. Typed level zero gives the bound-variable test;
shift-fixedness gives the shift test. Raw identity substitution on the core
slots establishes the existing code bound. The result therefore belongs to
the actual `SepR`/`RepR` recognizers and the existing ZF/ZFC Δ1-class unions.
Four typed axiom-proof constructors have literal values satisfying the
actual represented `Proof ZF` or `Proof ZFC` predicates.

The [fresh check](results/model-coded-schema-axioms-verification.json)
passes eleven axiom reports and ten callers, with standard Lean axioms and
zero warnings. It freshly checks the five local schema prerequisites, the
new module, and two pinned Foundation prerequisites: `SetTheory.Basic.Misc`
and `SetTheory.Basic.Axioms`. The [independent review](results/model-coded-schema-axioms-review.json)
binds the proof, audit, fresh objects and selected providers.

```sh
python -B Logic/Interpretability/ZFCinPA/check_model_coded_schema_axioms.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --lean /path/to/pinned/lean \
  --output /outside/new-empty-schema-check
```

The checker builds those eight units serially with one thread and 4 GiB.
The two Foundation outputs live in the scratch overlay. Unchanged cached
Foundation namespace branches are linked there to satisfy Lean's namespace
lookup; seven named boundary providers are checked, without attesting the
entire inherited cache. Nothing is downloaded or written into dependency
checkouts. `--prepare-only` checks provenance and prepares the overlay
without compiling. Its [maintained-default record](results/model-coded-schema-axioms-preflight.json)
is separate from the successful proof check.

The earlier missing-provider preflight, namespace-root failure and
development failures are retained. A generic axiom-carrier lemma avoids
expensive normalization of each concrete theory. The final audit needed
explicit numeral coherence and noncomputable proof-data callers.

Shift-fixedness remains an explicit restriction. This module does not yet
construct closure for arbitrary internal free-parameter matrices, interpret
the constructible or well-founded classes, or prove the PA C254/ZFC
consistency comparison.
