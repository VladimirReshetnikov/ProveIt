# Internal growG translation: author receipt

Author: `/root/controller_certificate`, 26 October 2026. This is author
validation of three new Lean files, not an independent review. The proposed
small interface and the existing `vac_eq` extraction were identified by
`/root/complemented47_review` in `research/ha-c222-internalization-audit.md`.
I read the complete relevant validator modules, the constructor/recurrence
clients, the finite circuit API, the Cantor bounds, the actual C222 template
and the finite Kalmar deduction interface before execution. I read all new
sources before each execution and again in their final form.

No accepted source, shared object, umbrella, status document or Git state was
changed. The separate earlier LV receipt received only its authorized updated
Lean-author-receipt hash; that change is not part of this proof packet.

## Exact result

`ArithmeticTemplates222` defines a literal finite constructor circuit and a
parameter-free Sigma0 graph for

```text
growG a b c = (c=a) -> ((c=b) -> forall_(wel a b) (a=b)).
```

Its graph is correct for arbitrary internal inputs in every IOpen model. Its
Nat specialization equals the actual `KCode222.growG` definition exactly.
The graph does not encode a new seed bundle or a replacement checker.

`ValidatorGrowG222.cProv_growG_literal` and `.cProv_growG` prove, for arbitrary
`V` with `ORingStructure V` and `V` satisfying IΣ1, that the unchanged internal
C254 validator proves this template at every internal a,b,c. The exported
`exists_growG_code` spells out the actual witness:

```text
exists d : V, ArithmeticHistory254.value d = growG a b c + 1.
```

The argument is finite. Cantor/component bounds prove `a < wel a b` and
`b < wel a b`. The existing `vac_eq` theorem then supplies
`(a=b) -> forall_(wel a b)(a=b)` by extracting the equality-vacuity component
from the genuine gated C254 bundle. The existing rho7 closure supplies
`(c=a) -> ((c=b) -> (a=b))`. Two finite Kalmar deductions compose these
proofs; there is no generalization of an open assumption and no additional
freshness requirement on c.

The focused checks include a=b=c, all labels zero, and c=wel(a,b), precisely
to retain those legal cases. They also check the literal code equation, the
actual bounded graph and the separate standard-Nat conclusion
`Code254.C254 (KCode222.growG a b c)`.

This is one all-internal axiom translation. It does not prove C222 seed
validity, C222/C254 refutation equivalence, a 215-machine runtime translation,
an internal equation/consistency equivalence, or an HA derivation. The use of
the existing classical C254 propositional interface is explicit.

## Frozen new sources and objects

Paths BB and ZP abbreviate `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/` and
`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/` respectively.

| Source | Lines | Source SHA-256 | Fresh object SHA-256 |
|---|---:|---|---|
| BB/ArithmeticTemplates222.lean | 42 | `e346d466e4778df946d385dc4b45855326957894019e627925c42fea803be962` | `24e69718e7c72d90e46e75efc602bf34146c719069980eaf97118c1d7ff8a0bc` |
| ZP/ValidatorGrowG222.lean | 63 | `2c90de565e1af9d018a8eced7ad158bed1a4d04ae4917e3f8c49fec1063291dd` | `7bbb2f0df284b2e214b8575ba79481ee2a4a15eac004f25e8b72bdd9e89900fe` |
| ZP/ValidatorGrowG222Checks.lean | 46 | `756fd5e74dd0d34220fcccff0a459c15eb63d568b3eddbe7037c3766045352a9` | `73386d8022dd4c1dd24a9946ba3dd95bc598b19de29c0a2b037a576e8fc74832` |

The compiler is Lean4.32, SHA
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The package manifest hash is
`95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.
Every command used `-M6000 -j1 -DElab.async=false`, with the private
`/tmp/growg222-controller-6p9201ob/lib` overlay and explicit package paths.
No broad Lake build, package download, Foundation rebuild or cap raise ran.

All seven final leaf commands exited zero: four authorized prerequisite
refreshes followed by the new circuit, adapter and focused checks. All six
final non-check logs are empty. The ten intended axiom reports each contain
only `propext`, `Classical.choice`, `Quot.sound`; there is no `sorry`, new
axiom or `native_decide`. Final successful commands took 22.78 seconds in
aggregate; maximum RSS was 1,825,004 KiB. The driver checked a 512MiB disk
reserve before every compiler invocation.

## Precise dependency boundary

The pre-execution selected inventory contains 118 custom prerequisite modules:
95 Foundation and 23 project modules. The source/object hashes of all selected
prerequisites and their recorded companions were authenticated and checked
again afterward. There are additionally 38 direct precompiled package/toolchain
import boundaries, pinned separately; their transitive package closure was
not freshly rebuilt or asserted as a new full attestation.

The historical quantifier cache had nine project logical source hashes that
no longer matched this checkout. Those old logical objects were excluded.
The accepted arithmetic215/current361 source-matching objects supplied the
current versions. The retained arithmetic215 receipt also supplied the
already-authenticated Foundation95 source/companion bindings. I rechecked
those SHA-256 bindings; this is cache reuse, not a new Foundation build-trace
or proof replay.

To verify the actual current interface rather than silently inherit the old
client objects, the following four current sources were freshly compiled in
order. Their source bytes were unchanged; the new private objects differ from
the historical objects and are recorded without claiming byte equality.

| Refreshed client | Source SHA-256 | Fresh object SHA-256 |
|---|---|---|
| ArithmeticHistoryRecurrence254 | `5d2bf146c7bed7d60e8297a911496d1009696bec858edb4f8be7c05fb99bdbb6` | `1f26cd8b6058516d82f9561d5138a4279a69fccd61f4e20143de6172c8a3bc31` |
| ArithmeticProofConstructors254 | `34d33aeb05b4b37a29659aa3d6e86281783fab70574a8352eded4560b6dfb875` | `209c6608e0cdd5c159271e43f8ee53dc3ee1d5e6d55b5f96d4b325a938d12f62` |
| ValidatorProvability254 | `372a7fbd58fb5d018951e3e23dc308062ad02546279620e1d67fb3d06e7845b6` | `e426150f45b59b6d3e9cdc09f8e8e4918558d09f4041fb46021121876c58c89c` |
| ValidatorQuantifierCore254 | `4afb9947d05cf713b74c16cb8162af5b0e6c03461ed87e21cbdf1da3303ea2f1` | `a5fd14c8a58c24a2cb89ba995164e243c5855bf64c36895e975a3fbed97e917f` |

Thus the final packet uses 114 reused prerequisites and seven fresh modules,
not a fresh full closure. Source hashes remain unchanged across the root's
concurrent unrelated merge/replay. All old provider objects remained unchanged;
only newly created private objects were written.

## Retained development evidence

An initial pre-execution import scanner omitted Lean's `public import` syntax.
The unexpectedly small Foundation closure exposed that mistake before any
compiler invocation. The scanner was corrected and the complete 118-module
inventory was frozen before execution; the initial unused inventory remains
in `/tmp/growg222-controller-tapa83wo/inputs.json`.

The four prerequisite refreshes and constructor graph passed on their first
runs. The first adapter run rejected the Nat wrapper's unparenthesized
`cProv_nat_iff.mp`; replacing it with `(cProv_nat_iff _).mp` fixed the
elaboration. The internal theorem and its assumptions did not change. The
final adapter and checks then both passed. Failed logs and exact source
snapshots remain separate from the final successful records.

The complete pre-execution inventory has SHA
`518dcb6476839e20f07e9b2f30de8f41eee1b26aff3e2c39a9b704e50336185c`.
Commands, source/object pins, all final and failed runs, axiom reports, resource
measurements and postchecks are preserved in the adjacent
`validator-growg222-replay.json`, SHA
`d3620d611969413ce66e1a3720d1c38832156d0773838a6bc752ba083e7092c3`.
The Python orchestration was newly authored and read before use; no historical
cache checker, archive script or incoming proposal program was executed.
