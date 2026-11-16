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

The [boundary](r2gic/boundary.json) binds the [frozen C254 row](../../../Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-graph-marked-rebuild-prototype/evidence/frozen/BusyBeaver/ZFC/ArithmeticRow254.lean)
at source SHA-256 `90c29554d76400618777a6139be5089220093a5effb2b0587f0d3ab497d0ca7c`
and object SHA-256 `31605fadd094293637d997b102f64ec2814da76d120a942aa0f17ef8d402b76e`.
Git `437804fcdd5550fec6ece3b6073c616690d4625f` contains those row source bytes.
The guard reads the absolute paths in its boundary and parent receipts. Its
current `--prepare-only` check fails on the recorded `Code254.lean` source
hash, and nine other historical source files have drifted. Six Foundation
object paths are absent from the recorded dependency root. Hash-matching
copies of four were located in the workspace cache. `HFS.Seq` and
`Bootstrapping.Syntax.Proof.Typed` remain unresolved in the locations checked.

Discharging the native theory's full `AxOK` premise remains separate work
before the final binary240 PA equivalence can be checked.
