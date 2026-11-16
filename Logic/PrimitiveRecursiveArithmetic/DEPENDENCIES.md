# iPRA source and provider inventory

The [unification plan](UNIFICATION-PLAN.md) uses two complementary scans.
Search the Git tree to find tracked importers, including sources outside a
sparse checkout. Follow Lean's parsed imports with the workspace's source
search path to identify the closure of a package or endpoint.

## Active source roots

Run [the import checker](Bridge/check-import-closure.lean) with no arguments
to enforce the portable and Foundation boundary checks. Pass explicit
module names to inspect their source paths, direct imports, and transitive
counts by namespace.

```sh
lake env lean --run Logic/PrimitiveRecursiveArithmetic/Bridge/check-import-closure.lean \
  --inventory ConciseIPRA.PR IPRADerivations Foundation IPRABridge \
  DiophantineConsistency.IPRAStandardAxioms BusyBeaver \
  BusyBeaver.ZFC.ArithmeticHistory222 Diophantine PAListCoding.ExactTrace \
  BoundedPAConsistency BoundedZFCConsistency ZFCinPA.ModelCodedFreeRenaming
```

The root Lake configuration uses the providers in
[`lakefile.toml`](../../lakefile.toml), Lean `v4.32.0`, Mathlib at
`81a5d257c8e410db227a6665ed08f64fea08e997`, and the
Foundation submodule at `32e1a0956a8622fad067328ca1959729a7634428`.
Transitive counts exclude the requested module and include the Lean runtime
sources. The printed header list includes two implicit `Init` entries, which
the direct counts below exclude. The command prints every direct import
and the transitive counts by namespace. The table was measured at
`435ab5dc3c`.

| Root | Direct imports | Transitive imports | Observed boundary |
| --- | ---: | ---: | --- |
| `ConciseIPRA.PR` | 1 | 1,975 | Canonical ordinary syntax and proof system with no Foundation or application dependency. |
| `IPRADerivations` | 137 | 3,103 | Ordinary Concise proof library, Mathlib, and the Lean runtime. The closure checker excludes Foundation, the bridge, and application modules. |
| `Foundation` | 455 | 3,088 | Vendored library umbrella. The upstream standalone manifest at the pinned revision uses Lean and Mathlib `v4.31.0`. ProveIt builds its own targets with the root toolchain. |
| `DiophantineConsistency.IPRAStandardAxioms` | 1 | 2,543 | Foundation and the local arithmetic statement modules. The closure excludes the successor-induction proofs, `IPRAStandardTheory`, and application endpoints. |
| `IPRABridge` | 1 | 2,606 | ConciseIPRA and Foundation arithmetic. The checker excludes the deep witness path, machines, consistency endpoints, and polynomial certificates. |
| `BusyBeaver` | 2 | 603 | `Core`, `KnownValues`, and the Lean runtime. The standalone [Lake package](../../Computability/BusyBeaver/Lean/lakefile.toml) resolves both local imports and has the same parsed closure. That package also declares `FirstOrder` and `ZF`. |
| `BusyBeaver.ZFC.ArithmeticHistory222` | 3 | 2,567 | Opt-in Foundation `IΣ₁` evaluator with the small Concise deduction and term-model modules. |
| `Diophantine` | 308 | 5,251 | Mathlib, the H10 constructions and existing PAListCoding interface. Its closure has zero Foundation, iPRA bridge, or BusyBeaver modules. Its independent build target is in the root Lake manifest. |
| `PAListCoding.ExactTrace` | 1 | 2,825 | Standard natural numbers and the Mathlib Diophantine and Chinese remainder interfaces. |
| `BoundedPAConsistency` | 31 | 2,751 | PA proof coding, model transport and specialized Foundation interfaces. |
| `BoundedZFCConsistency` | 20 | 627 | The sealed ZFC calculus and local `FirstOrder` and `ZF` libraries. |
| `ZFCinPA.ModelCodedFreeRenaming` | 1 | 2,669 | Foundation syntax, coding and arithmetic in arbitrary `IΣ₁` models. |

The [endpoint inventory](ENDPOINTS.md) records the exact theorem statements,
checks, and inputs associated with these roots.
The source gate also checks that `IPRASubSuccSelfNonzero` can be built with
its common term syntax and without the separate classical proof module,
and that `IPRANotBit` imports its code compiler without `PRANotBit`. The
classical interfaces retain their own checks.
The source gate also checks that the `Diophantine` umbrella is independent
of Foundation, BusyBeaver, and the ordinary iPRA and bridge layers.

## Tracked direct imports

The following scan identifies syntactic import statements. It includes active
sources, tests, generated source copies, and proof packets. The header walk
above resolves which of those files Lake actually reads for a target.

```sh
git grep -l -E '^[[:space:]]*((public|meta)[[:space:]]+)*import[[:space:]]+(all[[:space:]]+)?(ConciseIPRA|IPRADerivations|IPRABridge|DiophantineConsistency\.IPRA[^[:space:]]*)\b' \
  HEAD -- '*.lean'
```

At `64ec2f572c` this scan found 4,699 files. Of these, 672 belonged to the
root Lake source directories of BusyBeaver, ConciseIPRA, the bridge,
IPRADerivations, or DiophantineConsistency. The Diophantine root directory
had zero direct imports in this scan. The rest came from the research and
review trees, including 3,563 paths in DiophantineConsistency review
bundles. Those counts include multiple copies of some module names. In
particular, the active `DiophantineConsistency.IPRAStandardTheory` has
separate object providers in historical staged replays. Match an object
to the selected provider and closure before importing it.

## Pinned and experimental providers

| Source family | Maintained entry point and provider rule |
| --- | --- |
| PA literal tables and staged theorem closures | Follow the [PA inventory](../../Computability/BusyBeaver/Research/PA/README.md) and its exact table and stage receipts. The [primary replay](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/native-endpoint/README.md#conciseipra-export) and [PA1944L replay](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa1944l/README.md) specify the selected `LEAN_PATH` order. |
| PA195 and PA196 supplier packages | Use the candidate's [PA195](../../Computability/BusyBeaver/Research/PA/verification/other-machines/pa195/ipra/README.md) or [PA196](../../Computability/BusyBeaver/Research/PA/verification/other-machines/pa196-vs-u208/ipra/README.md) guide for generated table headers. The independent PA196 and PA209 manifests under `jamesyc-upstream` select their own Foundation providers. |
| K215 Lean and Rocq | Use the [verification guide](../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md) for the exact model, table, source and compiled-object hashes. Lean and Rocq have separate replay inputs. |
| ZFC equation transfer | Use the root Lake target for current sources, or the ordered [nine-variable author replay](../../Computability/DiophantineConsistency/reviews/nine-variable-ipra-complete-author-ledger/README.md) for the historical proof. The historical replay supplies its own Lean sources and objects. |
| Concise scalar checkers and proof packets | Use the [checker artifacts](ConciseIPRA/Artifacts/) and the [packet index](docs/proofs/README.md). A packet with its own Lake manifest, versioned checker, or inspected sources keeps that versioned entry point. New checks for shared ordinary arithmetic belong in the root library. |
| DARC-iPRA research packet | The [packet](docs/proofs/foundations/darc_ipra_framework_2026-11-16/README.md) targets `Prf PRAAx`. Its published checks cover its reference algorithms and report. The Lean blueprints and preliminary structural kernel sit outside the root Lake libraries. |

For a staged replay, capture the ordered provider paths, resolve duplicate
module names using that order, and record the exact source, `.olean`, and
companion hashes used by the relevant check. Validate a generated header
against the source data selected by its generator. The provider order is
part of the replay receipt.

The K215 portable Lean driver's source walk at `d3b635d18e` selects 168
project modules and `Init`. All 168 source blobs match the tree at the
unification plan commit `fab7ff7033`. The published dense and native table
hashes and `sites215.json` hash also match. The Rocq extension tree and
undecidability submodule revision match those recorded at the plan commit.
The [pinned K215 receipts](../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md)
give the compiler evidence for their recorded source closures. The
earlier phase-15 receipt documents a 176-module Lean endpoint.
