# Cancel finite free-variable shifts in internal proofs

For every internal theory T and every internal formula p, a represented proof
of shift(p) yields a represented proof of p. No shift-fixedness or closedness
condition on p is used. The arithmetic model is an arbitrary model of IΣ1.

The construction views p as a one-slot formula whose bound slot is unused.
Its free instance is exactly shift(p). Universal introduction followed by
specialization at free variable zero returns p, using the checked binder
absorption identities. Iterating this construction cancels any externally
finite number of shifts. The iteration index is an ordinary Nat; this module
does not assert induction over arbitrary internal proof codes.

This supports a proposed compiler for a fixed proof template with arbitrary
internal predicate parameters. A finite buffer can accommodate both universal
introduction and explicit shift rules, then be cancelled at the conclusion.
The compiler, its predicate translation, and Collection are separate obligations.

The [56-line source](Lean/ZFCinPA/ModelCodedShiftCancellation.lean) and
[audit](Lean/ZFCinPA/ModelCodedShiftCancellationAudit.lean) passed on the first
proof build: six axiom reports, nine callers, standard Lean axioms only, and
zero warnings. Source and audit took 2.744s and 2.128s. The
[original record](results/model-coded-shift-cancellation-verification.json)
and [history](results/model-coded-shift-cancellation-history.json) retain the
unbuilt preparation and exact successful source, audit, guard, and inputs.

The checker selects eleven syntax ancestors from the AtomicVacuity evidence;
neither that parent's fresh client nor Cantor is imported. Six direct external
source/object boundaries, the actual first Init/Omega providers, compiler,
dependency pins, and all 47 inputs are checked before and after compilation.
The supplied complete Foundation namespace is reused, not independently rebuilt.
Compilation uses one thread and a 4GiB limit, with no dependency build or download.

```bash
python Logic/Interpretability/ZFCinPA/check_model_coded_shift_cancellation.py --output /tmp/shift-cancellation-replay
```

Repository, dependency, parent-evidence, source/audit, project-cache,
namespace-cache, compiler, and library paths can be overridden. Explicit
library paths replace default discovery and must include all required roots.
The portable runner is byte-identical to the executed guard. Packaging adds
one unbuilt preparation using maintained defaults; no additional proof replay,
relocated-cache test, or rejection control is claimed. The
[review wrapper](results/model-coded-shift-cancellation-review.json) preserves
independent source/proof review and this additive preparation.
