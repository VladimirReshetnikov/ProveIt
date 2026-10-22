# One checked Rocq implication core for both K215 proof families

Baseline: `VladimirReshetnikov/ProveIt` at
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

This is an incremental implementation of existing shared-core research. It uses
the six-goal, 58-detachment plan already archived in
`verification/k215/simplification/phase12/upstream-merge/inputs/Research/ZFC/k225-formal/rho8cd/`.
At this baseline, that plan is an archived upstream proposal; the production
`rho8cd/derivation_core.txt` still contains the earlier three-goal plan. The new
work here is its Rocq rendering and the concrete `CD222` adapter, so both the
dominated-row and unrestricted implicational clients actually use one core.
The earlier `shared-proof-core/rocq_core` proposal supplied the initial renderer
and the unchanged `DomRho8` compatibility adapter; its K/S/Peirce extension used
five additional detachments. Attribution and source hashes are in `provenance.json`.

## Mathematical interface

`Language A` contains a binary operation `imp`, a reflexive relation `below`,
and two laws saying that either argument embeds into an implication.
`Restricted L T` says that `T` is closed under modus ponens and contains

`((c -> u) -> a) -> ((a -> c) -> (b -> c))`

whenever `below u a`. The direct proof derives all unrestricted instances,
composition, prefixing, K, Peirce and S. It needs no truth constant, decoder,
injective constructor, normalization equation or arithmetic assumption.

The `DomRho8` adapter supplies natural-number codes and the existing Cantor
pairing growth bounds. Its `DomImp` record keeps the original truth field for
compatibility, although the core does not use it. The new `CD222` adapter
uses a local language on natural numbers with domination always `True`:
`W_r8` ignores the restriction and `W_mp` supplies modus ponens. It imports
the generic core directly, without the numeric `DomRho8` adapter. Four short wrappers recover the exact
`thm_K`, `thm_P`, `thm_B`, and `thm_S` types consumed by the current clients.

## Size of the replaced proof sources

| Source group | Lines | UTF-8 bytes |
| --- | ---: | ---: |
| Production `DomRho8.v` | 1,169 | 22,673 |
| Production `CD222.v` | 230 | 22,865 |
| Production total | 1,399 | 45,538 |
| Shared generic core | 302 | 14,787 |
| `DomRho8` adapter, production `Stdlib` spelling | 54 | 2,310 |
| `CD222` adapter | 38 | 1,611 |
| Proposed total, production spelling | 394 | 18,708 |

The combined replacement removes 26,830 bytes (58.92%) and 1,005 lines (71.84%).
The locally checked Coq 8.18 spelling removes three bytes on each side:
45,535 bytes before and 18,705 after, with the same absolute saving.
The table counts all three proposed proof sources, not just either adapter.
It does not count the untrusted producer, derivation data, test clients,
inherited dependencies, or archival baseline. The old reflective proof's 735
instructions and the new 58 detachments are different units: explicit
substitution instructions are replaced by ordinary proof-term instantiation.

## Exact compatibility boundary

Preserved and type-checked: `DomImp` and its fields, `rho8_all`, the unchanged
client theorem `thmDom_iff`, and the four `CD222` facade theorems. The new core
and adapter additionally expose composition and prefixing.

Removed implementation names include the old `Certificate` interpreter and
the generated `cd_0` through `cd_106` lemmas. No selected production K215
client references those names. A wider consumer that imports these internal
names needs a compatibility module or a deliberate migration. This is not a
claim to preserve every accidentally exported identifier of the old files.

The focused client `BasisClients.v` contains a verbatim segment of production
`Prop222.v`: identity, the `der222` datatype, deduction, discharge and weakening.
Only its imports were reduced to actual dependencies. It is a real client
fragment, not a replacement axiom, but it is not a compilation of the entire
`Prop222`, `G222`, `Interp222`, or `Complete222` modules.

## Reproduce

With Python 3 and `coqc`/`coqchk` on PATH:

```sh
python3 reproduce.py --out /tmp/k215-shared-rocq
```

The driver checks pinned input hashes and exact regeneration, creates separate
baseline and candidate trees, compiles the source dependency closures, checks
all expected assumption reports, and recursively kernel-checks both the type
audit and the propositional client. There are no admissions, new axioms or
trusted native-computation checks. The inherited files use the Coq 8.18
standard-library spelling `Coq` in place of production Rocq's `Stdlib`.
All other inherited production code is unchanged.

The included evidence records the actual focused run under Coq 8.18.0 and
OCaml 4.14.1. It must not be read as a new execution of the production Rocq
9.1, 237-module ZFC endpoint build. Local times in the receipts are single-run
observations, not controlled whole-project performance measurements.

## Production integration

1. Add `DominatedImplication.v` to the K215 source list and dependency plan;
   its compilation precedes both adapters. Replace `DomRho8.v` and `CD222.v`
   using the included proof-source patch.
2. Update `rocq/rocq-extension/regenerate215.py`: the `DomRho8` branch should
   run the new renderer and install its adapter; the `CD222` branch should
   install its adapter. Preserve these changes through regeneration rather
   than hand-editing generated output only.
3. Update the 215 source order and hashes in the existing manifest/receipts
   through the normal reviewed process. Do not relabel old evidence as a
   check of new inputs.
4. Compile the affected real clients and endpoint with the pinned production
   Rocq 9.1 toolchain, inspect the sparse and dense endpoint assumption
   reports, and run the recursive endpoint kernel check. The focused result
   here provides the local proof and interface evidence for that integration.

The Turing-machine table, state count and endpoint statements are unchanged
by this proposal. No claim of a new 214-state candidate or a new internal
ZFC formalization is made.

## Production spelling and design choice

`proof-sources-rocq91.patch` contains the same complete source change with
`Stdlib` instead of `Coq` in the numeric adapter. It adds three bytes and
passes patch application checking, but is not a claimed Rocq 9.1 compilation.
The universal-relation CD222 adapter costs nine lines and 348 bytes compared
with routing the ordinary calculus through the numeric adapter. It separates
ordinary implication logic from numeric domination and mirrors the Lean
instantiation. The supplied source totals include this chosen adapter.
