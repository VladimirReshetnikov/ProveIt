# K215 proof audit and next simplification

Repository examined: `VladimirReshetnikov/ProveIt`, commit
`b6c7087477e51c017003bd729e712c8969733223` (2026-10-21).

## What is already done

The user's premise is supported by the retained endpoint sources and build
records, but the current checkout has already progressed beyond the original
proof: phases 1–3 of proof simplification are present. These must be credited as
existing results, not claimed as new work.

The authoritative index is
`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md`.
The current Lean closure has 185 project modules rather than the 204 in the
original fresh build. Its phase-3 check rebuilt nine affected modules and reused
176 objects with retained bindings. It is explicitly an incremental check, not
a second fresh replay. The Rocq original closure has 237 sources (195 pinned
reference sources and 42 K215 sources), with retained recursive `coqchk` evidence.

Existing reductions, from `verification/k215/simplification/README.md`:

| Source | Original bytes | Current bytes |
|---|---:|---:|
| Lean dominated implication | 689857 | 35185 |
| Lean AX routine | 202222 | 7563 |
| Lean source certificate data | 653569 | 456548 |
| Lean site-coverage facade | 107243 | 14916 |
| Lean register determinism | 17209 | 12988 |
| Rocq dominated implication | 921691 | 22673 |

These are repository-recorded source sizes, not new measured speedups.
Phase 2 already eliminated 16 reverse certificate modules by proving symmetry.
Phase 3 already uses 61 small bootstrap lemmas and 81 conditional schemas for
the dominated implication, one general enumerator theorem for both starts,
and direct composition of 105 existing site-coverage blocks. The corresponding
Rocq dominated-rule certificate has 735 instructions. Proposing these changes
again would duplicate completed work.

## Actual architecture

`Lean/BusyBeaver/ZFC/KEndpoint215.lean` (53 lines) is already a small facade.
It supplies a dense-state commuting map, register engine contracts, the blank
bootstrap, site coverage, and source/program equivalence to the generic
`KEndpoint.blank_halts_iff_zfc_refutation`. Its public endpoint is

```
BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot.
```

The Rocq sparse facade `rocq-extension/coq/215/Correct215.v` is 19 lines;
the dense facade `CorrectDense215.v` is 18 lines. Shortening these final
compositions has negligible value. The work is in semantic calibration and
generated certificates.

The Lean source proof currently relates the optimized source to `DagPerm`
using 2240 segment entries. Every offset is zero; nevertheless it instantiates
the more general integer-offset checker. `KSource215Data.lean` is 456548 bytes,
2576 lines, and its comments report a 179-node path-program DAG. The paper's
202-node source figure uses a different source representation and is not the
same metric. The target DAG has maximum height 178. The zero-offset checker
`RMBisim` currently decodes only 128 binary path bits; the offset version
decodes 512. Replacing the offset checker naively with the old zero-offset
checker would therefore be invalid. Parameterize or remove this technical
bound first if taking that route.

## Recommended proof organization

1. Preserve the exact already checked K215 endpoint as the base theorem.
2. For a candidate obtained by a small transition-table change, prove a direct
   whole-tape machine simulation from that base rather than reconstructing its
   numerical calculus, enumerator, register program, compiler and startup.
3. Prove a generic positive-block simulation theorem once. For deterministic
   partial transition systems, terminal agreement and simulation of each source
   step by a nonempty target block imply halting equivalence. The reverse
   direction follows by strong induction on the length of a terminating target
   execution, consuming the positive block. A second simulation certificate is
   unnecessary. Empty blocks without a well-founded auxiliary measure do not
   justify the reverse implication.
4. Isolate the new machine's evidence into literal table data, a local invariant,
   and finite local transition obligations. Check these small obligations in
   the kernel. This makes the *incremental* proof of CM215 easier; it does not
   erase its dependence on the already established K215 endpoint.
5. For future large source transformations, move from repeated long path codes
   to a quotient of the finite test/effect control-flow graph, with a verified
   normalizer. Preserve exact halt/control behavior and increment counts. The
   expensive source certificate should be replaced only after a concrete
   soundness lemma and exact binding to the literal source are checked.

The new `PositiveStutter.lean` supplies item 3 using only Lean's `Init` import;
the analogous `PositiveStutter.v` was compiled in Coq 8.18.0 and recursively
checked with `coqchk`. Both Coq public endpoints are closed under the global
context. This is a standalone generic theorem, not another replay of the
repository's Rocq 9.1.0 endpoint.

The CM215 concrete proof is in `CM215Tables.lean`, `CM215Invariant.lean`, and
`CM215Transfer.lean`. The maximum local simulation length is three steps.
Its invariant uses only the scanned bit and its two neighbors. The newly
compiled `CM215CoreBridge.lean` binds the source machine to the exact existing
`KDense215.machine215` under the repository's finite-support tape semantics.
`CM215Dense.lean` defines `machineCM215 : Machine 215` from the literal target
rows and proves the Core-machine blank-halting equivalence. All these new
transport endpoints depend only on `propext` and `Quot.sound`.

The separate `integration/CM215Endpoint.lean` composes this checked Core-machine
equivalence with `KEndpoint215.blank_halts_iff_zfc_refutation`. It is supplied
for checking in the full repository and is explicitly outside this session's
fresh standalone build claim. The generic `calibration_transfer` theorem in
`CM215Dense.lean` was freshly checked and exposes the existing base proposition
as an ordinary theorem parameter, not an added axiom.

## Trust and claim boundaries

The retained Lean endpoint reports list only `propext`, `Classical.choice`,
and `Quot.sound`. The retained Rocq endpoint reports are closed. Rocq's global
import context contains three utility axioms, but the published endpoint
dependency reports contain none of them. A global-context listing is distinct
from an endpoint-dependency listing.

The existing README expressly distinguishes external proof-assistant theorems
from a proof encoded in ZFC's own syntax; an internal PA endpoint is also not
claimed. A direct finite-machine transport theorem preserves whatever base
internal statement is available: if ZFC proves the K215 equivalence and proves
the local transport, then it proves the CM215 equivalence. Our small transport
argument does not require another set-theoretic calibration.

We inspected the retained original build records; we did not rerun either
complete 185/237-module closure in this session. New standalone proof checks
must be reported separately from those original retained checks.

## Further questions

* Can every candidate within a small table-edit neighborhood of K215 be
  classified using a fixed finite-window invariant synthesis procedure?
* Can local history bits always be replaced by inductive tape predicates in
  these marker-fold candidates, or are ghost tags sometimes necessary?
* Can the 2240-entry all-zero source certificate be replaced by a small
  canonical test/effect graph certificate checked once in Lean and Rocq?
* Which candidate minimizes new proof obligations under transport from the
  checked baseline, as distinct from minimizing its stand-alone source proof?
* Can the elementary machine/compiler layer be isolated in a weak arithmetic
  theory and linked to a separately formalized internal ZFC equivalence?
