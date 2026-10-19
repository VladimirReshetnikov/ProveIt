# Internal translation of global-image collection

The unchanged [`R2Gic`](Lean/ZFCinPA/R2Gic.lean) proves the native GIC
translation for arbitrary internal two-variable matrices in IΣ₂ models.
It retains the ordered odd labels, freshness conditions and both matrix
clauses. Its literal encoding equations preserve the double negation and
negated universal quantifier in the validator's formula.

The [actual check](results/r2gic-verification.json) passes 15 named axiom
probes and 15 typed callers. Source and audit took 9.737 and 2.716 seconds,
using default proof limits, one thread, 4,096 MiB and a shared 120-second
deadline. All reported axioms are standard Lean axioms. Six existing source
warnings remain: two unused section instances, two unused variables and two
unused simplification arguments. The audit has no warnings.

The guard selects 49 exact project prerequisites, eight external boundaries
and Init/Omega from the checked R2Main and native-GIC congruence results.
It retains their warning and cache-scope disclosures, including the older
congruence record's absent namespace-overlay and option metadata. It uses
the existing R2Main namespace overlay without claiming to attest the whole
namespace or rebuilding dependencies. The
[publication](results/r2gic-publication.json) and [history](r2gic/history.json.gz)
preserve the reviewed source, guard, bindings and raw logs.

Discharging the native theory's full `AxOK` premise remains separate work
before the final binary240 PA equivalence can be checked.
