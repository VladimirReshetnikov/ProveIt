# Independent source and encoding audit

This directory preserves compact research scripts, selected exact sources, and finite receipts. The searches here found no source DAG with 205 nodes. This is a bounded heuristic-search result, not a lower bound on the program or Turing-machine state count. `halt_specialization.md` records a later positive source-equivalence result whose compilation is evaluated elsewhere in this packet.

## Results and exact scopes

| Investigation | Recorded extent | Best result |
|---|---:|---|
| Global safe reassociation, original K219 | 32 layers; 1,897,711 distinct candidate-root hashes | 206 DAG nodes |
| Global safe reassociation, neutral rho6 variant | 30 layers; 1,069,124 distinct candidate-root hashes | 206 DAG nodes |
| Global safe reassociation, specialized reuse-E halt test | 8 completed layers; 239,819 distinct candidate-root hashes | 206 DAG nodes |
| Occurrence-local safe reassociation | 15 layers; 1,812,417 distinct candidate-root hashes | 206 DAG nodes |
| Reduce maximum source zero run, DAG cap 208 | 19 layers; 354,668 distinct roots | Zero run 5, 208 DAG nodes |
| Reduce maximum source zero run, DAG cap 206 | 20 layers; 372,228 distinct roots | 14 remaining six-zero-prefix occurrences |
| Joint closed-region RePair, no zero-run bound | 2,000 trials | 208 DAG nodes, zero run 8 |
| Joint RePair, original source, historical 20% freezing | 2,000 trials | 206 DAG nodes, zero run 6 |
| Joint RePair, rho6 source, 8% DAG-consistent freezing | 3,000 trials | 206 DAG nodes, zero run 6; 462 trials attained 206 |
| Remove state 198, replace its sole incoming row | All 872 remaining single-transition actions | No action met the tested interfaces |

For the beam searches, a recorded root is counted before the zero-run/DAG cap is applied; it is not a fully compiled machine. Counts from different searches overlap and should not be added as though they were distinct programs. The beams retain a fixed quota per DAG-size bucket, so they do not exhaust their state spaces. Recursive Python hashes are used only to avoid revisiting search candidates. A collision could lose an opportunity; successful artifacts are checked using exact trees and two independent CFG resolvers.

Global reassociation replaces all occurrences of an identical subtree together. Occurrence-local reassociation changes one occurrence, allowing formerly shared occurrences to acquire different parses. Both use the control-safe rule `((A,B),C) <-> (A,(B,C))` when A has no escaping break and C has no escaping continue. Successful reported improvements are checked by the complete guarded source CFG, not by the syntactic criterion alone.

RePair jointly reparses maximal concatenations of closed source subtrees. The un-frozen baseline has 86 atoms, 11 maximal words, and 976 symbols. The zero-run-aware version rejects grammar substitutions that cannot meet the requested bound even under a minimal right-fold completion. The historical 20% freezing run predates the current per-DAG-node freezing rule; its receipt is retained as a research snapshot, and the current script is not claimed to reproduce its histogram. The rho6 3,000-trial receipt combines the original checkpoint for seeds 0 through 2899 and a fresh exact replay of seeds 2900 through 2999, because the original script skipped writing its final checkpoint when the last trial rejected. The portable script fixes that output-only issue.

## A positive source result that does not yet save a state

`artifacts/zero5_208.sites.json` is an exact CFG-equivalent reassociation of K219 with 208 DAG nodes, 4,744 leaves, depth 37, and maximum zero run five. `scripts/verify_zero5.py` independently rechecks that result. The historical discovery used unseeded random tie breaking, so its exact search trajectory is not replayable; the saved artifact is. The portable discovery script now accepts a fixed `--seed`.

A protected context-aware compilation attempt needed 234 working states, including one forced alias split. Its receipt is retained to distinguish the source improvement from a useful machine improvement. That compiler was a discovery heuristic, not an optimal compiler or a lower-bound argument. Reducing zero runs is potentially valuable because it can shorten a return scanner, but the physical arithmetic/decoder sharing must be preserved at the same time.

The compact decoder inventory records 15 states with multiple source-subtree bindings, 34 decoder states protected by arithmetic roles, and seven transition rows with mixed logical roles. Direct right-moving primitive entry actions can still depend on earlier PC bits: CI0/CD0 both use 0R14, CI2/CD2 both use 0R56, and CI8/CD8 both use 0R39 in some contexts. Choosing entries solely by the final opcode and register can therefore be unsound.

## Representative negative results

Deleting native state 198 and changing its sole incoming row `(66,0)` leaves 872 possible actions using the other 218 working states. The exhaustive action screen first checks the full zero-CD8 interface at source ordinal 0. Only `0L97` passes. That action then fails the remaining tested positive-CD8/CI8 interfaces even when the appended spare value is allowed to range from zero through four. This rules out that narrowly specified one-row rewrite under the tested reusable interface, not every possible implementation without state 198. The proof-search limit is a limitation of the search; a failure is not a semantic counterexample unless separately analyzed.

A fresh threshold-eight abstract induction on K219 identifies unreachable ordinals 4607, 4719, and 4720; CD6 at 4606 and CD1 at 4718 are forced zero. Deleting the closed, forced-zero final transfer from register 1 to register 6 nevertheless increases the DAG count from 206 to 207. Replacing dead code or known-no-op regions by existing subtrees did not improve that count in the recorded tests. These are contextual optimization opportunities with measured costs, not evidence that unreachable code must remain.

The independently verified NOP219 source inserts six leaves at `[4597,4603)`. Its fresh inductive invariant proves four inserted body leaves unreachable; only two zero decrements execute. Exact contraction matches all 6,166 original outside guarded edges. Its full runtime replay proved 6,175 interfaces in 1,508,163 symbolic steps. See `report/nop.tex`, `machines/nop219`, and the packet's main replay for the complete alternative machine.

## Reproduction

Use Python 3.10 or later, without `-O` or `PYTHONOPTIMIZE`. From the packet root, first extract and verify the pinned inputs. Choose a new output directory:

```sh
python verification/replay.py --quick --output-dir /tmp/k219-audit-inputs
export PROVEIT_K221_PORTABLE=/tmp/k219-audit-inputs/inputs/K221_Construction_2026-10-20/portable
python research/encoding/audit/scripts/verify_zero5.py
python research/encoding/audit/scripts/check_nop_source.py --out /tmp/nop-source-audit
python research/encoding/audit/scripts/verify_halt_specialization.py --variant reuse_e --out /tmp/halt-source-audit
```

The full runtime proof is replayed by omitting `--quick` in the main verification command. `environment.py` checks the exact pinned `source_language.py` hash before importing it. The search scripts use the extracted sibling K219 source by default; they write only to their requested output directory.

Representative search commands matching the recorded beam parameters are:

```sh
python research/encoding/audit/scripts/dag205_search.py --steps 32 --quota 100 --maxdag 208 --seed 219205 --out /tmp/dag-global
python research/encoding/audit/scripts/dag205_search.py --source machines/rho6_219/sites.json --steps 30 --quota 60 --maxdag 208 --seed 219205 --out /tmp/dag-rho6
python research/encoding/audit/scripts/local205_search.py --steps 15 --quota 25 --maxdag 209 --seed 205218 --out /tmp/dag-local
python research/encoding/audit/scripts/forest_repair.py --trials 2000 --out /tmp/re-pair-full
python research/encoding/audit/scripts/forest_repair.py --source machines/rho6_219/sites.json --maxzero 6 --freeze .08 --noise 1.5 --trials 3000 --out /tmp/re-pair-rho6
python research/encoding/audit/scripts/search_spare198.py --out /tmp/delete198
```

These discovery runs can take minutes and consume substantial transient memory. The saved-artifact verifiers finish quickly. `receipts/script_origins.json` records the hashes of the original research scripts before portable path/CLI edits. Search-result counts are empirical receipts; they are not proof-assistant certificates.
