# Source-declared 16-module path for the current14 67/106 endpoint

This is a **read-only preflight**, not a build or source snapshot. The
[ordered manifest](result.json) traverses `ModelCarrierScaled`,
`ModelCarrierSyntax`, `ModelArithmetic`, `IPRAExpressionNative`, and
`HACurrentEquation2011`. It covers 1,007 source modules: 991 shared with
the authenticated fresh current14 base and 16 additional modules in
source-declared topological order. All shared source hashes and declared
imports match the pinned base manifest. The run rechecked 9,910 base
object/companion presences or absences and 4,151 recorded direct-input
edges (1,093 distinct paths), twice, against the pinned successful base
state; external main/companion candidates under the ordered roots are
also recorded and rechecked.

The five added direct external module names are
`Mathlib.Algebra.MvPolynomial.CommRing`, `Mathlib.Algebra.Order.Ring.Abs`,
`Mathlib.Algebra.Order.Ring.Cone`, `Mathlib.Data.Int.Basic`, and
`Mathlib.Data.Int.Order.Units`. The inventory records candidates rather
than claiming which objects Lean would choose or certifying their complete
package-transitive dependencies. In particular the earlier Matrix collision
remains unresolved. The companion and root observations are point-in-time;
transient changes and runtime/dynamic imports are outside scope.

A new focused client would need to reproduce the checked model-level
`sameZero106` proof from `ModelCarrierCurrent` and the small general
same-zero-to-polynomial-bridge proof from `HAExpressionSameZero`, then
compose the existing `HACurrentEquation2011.polynomialBridge`,
`IPRAExpressionNative.equivalence_of_bridge`, and standard-theory transfer.
Those client steps and 16 source modules have **not** been compiled in this
preflight. This avoids the unrelated 86-equation stack imported by the
full `ModelCarrierCurrent` closure; it does not eliminate the need for
all-model reasoning or transfer correctness. See the separate
[direct-transfer plan](../normalized106-fresh-base-direct-transfer-plan/README.md).

[preflight.py](preflight.py) pins the lakefile, scanner and base evidence,
rejects absent/drifted sources or base objects, unexpected extension or
external counts, source cycles, missing external candidates, and
same-module candidate hash disagreements. It rehashes observed sources and
candidate inventories at the end. The manifest lists source paths/hashes,
not an immutable copied source tree. A later build needs a source snapshot,
actual `lean --deps` and provider/companion/shadow checks, collision review,
resource bounds and independent driver review. `PASS` here is not build
authorization or evidence of successful compilation.

Corrected preflight session 11672 exited 0; the separately captured
[terminal observation](terminal-observation.json) pins source and result.
A first draft exited 1 due to a local Python variable-shadowing bug before
producing a manifest; it was corrected before the reported run. No Lean
process was invoked. To rerun without overwriting evidence:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/normalized106-current14-sixteen-source-preflight/preflight.py > /tmp/normalized106-preflight-rerun.json
```

Preflight SHA-256 `6a9e06d558e0ffa7167fa57460863df0c812e6cf132b1469f8ae6325983697d7`;
result SHA-256 `f159489a58b1804d327a35b98ae75e64d746efe4605de0ce8a25ef3d92ca70b2`.
