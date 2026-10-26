# The literal decimal machine and the existing consistency predicate

Date: 2026-10-25. Author: controller_certificate. Independent reviewer and
fresh endpoint-check replay: ROOT.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| DecimalMachineZFC.lean | 778af71680ec6aadd9858d30ace87c25012ac6b9dac02e2a483094401fc06107 |
| DecimalMachineZFCChecks.lean | 598220ac30d8d4700c0918974cf4658fe4fec7041d64ab4896b4badec47424d0 |

ROOT read the complete30-line module,25-line checks, actual KEndpoint215
source and complete Bridge source before executing the new endpoint checks.
The author freshly compiled the new module and checks. ROOT independently ran

```sh
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/DecimalMachineZFCChecks.lean
```

This exited0, including after the separate KZip verification described below.
All four printed axiom sets contain only `propext`, `Classical.choice` and
`Quot.sound`; the decoder conjugacy itself uses only the first and last.
There are no new axioms or admitted proofs.

The first theorem composes the actual715-digit decoder's proved dense-table
conjugacy with the current literal KEndpoint215 halting/refutation theorem.
The second takes negations and uses the existing `DiophantineConsistency.ConZFC`
definition, exactly `¬ BProv ZFCax_s [] Form.fBot`. It does not introduce a
replacement consistency predicate or assume a machine calibration premise.

The original168-module dependency run completed with104 authenticated cached
objects and64 freshly compiled modules. See its full [build record](machine215-current-closure-build.md)
and [completed source/object receipt](machine215-current-closure-completed.json).
ROOT reauthenticated all168 source hashes,167 unchanged object hashes,
compiler and Init. A differing KZip object was investigated: its historical
bytes differed from the original cache in exactly the embedded worktree path.
ROOT then read and freshly compiled the entire actual KZip source, recorded
its new object hash, and freshly repeated the closed endpoint checks. The
original104/64 boundary and this extra verification are recorded separately;
no claim of a fresh rebuild of all168 sources is made.

The inherited Bridge module needed two cached bundles. ROOT reauthenticated
all103 current source files against62ff and both reused object hashes; the
[durable receipt](bridge-dependency-cache-current.json) preserves that scope.
No older mismatching machine endpoint object was substituted for the checked
current endpoint.

The Diophantine/native-tableau calibration and internal object-ZFC proof
remain required. This closed theorem concerns the actual printed machine;
it does not yet prove the maintained polynomial equivalent to consistency
and does not assert that ZFC is consistent.
