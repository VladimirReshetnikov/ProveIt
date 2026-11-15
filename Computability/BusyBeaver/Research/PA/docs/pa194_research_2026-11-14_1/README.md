# PA194: comparison, reductions, and three new physical variants

**Result:** this investigation did not obtain a justified blank-start machine with fewer than 194 working states. It does deliver three new 194-state machines, complete literal tables, an elementary written iPRA proof of their halting equivalence to their exact GD parents, a current-corpus comparison, and reproducible research toward a reduction.

Start with [the report](report/report.pdf) and its [LaTeX source](report/report.tex). The report includes all three complete transition tables and an appendix covering all 85 distinct named designs recognized in the pinned collection.

## The delivered machines

| Machine | Working states | Literal rows | Parent blank initialization | New blank initialization |
|---|---:|---:|---:|---:|
| PA194GD_SF | 194 | 388 | 58,154 | 58,150 |
| PA194GDH_SF | 194 | 388 | 57,922 | 57,918 |
| PA194GDHS_SF | 194 | 388 | 57,768 | 57,760 |

These are deterministic single-tape binary machines on a two-way infinite tape. The tape is entirely zero initially; the head starts at coordinate zero. Dense tables use working states 0 through 193, start 0, and halt label 194. Every move is L or R. Native tables instead use start 74 and halt 254; native label 194 is a working state. The halt label is not counted as a working state.

Each child combines a four-row entry-history selector with two guarded three-step-to-one-step return shortcuts. All six changed rows execute during blank initialization. Every working state is graph-reachable, and the three graphs are mutually distinct and different from every retained prior representative even after state renaming, tape reflection, global symbol exchange, and erasing terminal-entry write/move decorations. This is a novelty statement relative to the pinned recognized corpus, not a worldwide priority claim. The patch ingredients themselves come from earlier designs; their compatible composition on these three GD sources and the resulting exact tables are new here.

| Dense table | SHA-256 |
|---|---|
| `machines/PA194GD_SF/machine.tm` | `c19098ea2ae9b39f00c4fce73d260cd87f3968a262011e7f68aa8430afcfae7c` |
| `machines/PA194GDH_SF/machine.tm` | `b6b216161500262a93975588e9f3ff54802e6451557b4d6df521a993555a9659` |
| `machines/PA194GDHS_SF/machine.tm` | `5f528318755696427d48643e5e37d166853c0b124430a06ae503ed3fcd7589d1` |

## The theorem and its dependency boundary

For each exact parent M and delivered child N, let H_X(t) mean that X has halted by time t, using an absorbing arithmetic run function. The written proof establishes:

    iPRA proves H_M(t) -> H_N(3t), and H_N(t) -> H_M(3t).

It uses the actual table rows, four selector cases, twelve guarded shortcut cases, primitive-recursive clocks and quantifier-free induction. It applies to a common finite-support initial tape in native state 74, hence to the blank tape. The simulation does not assume Con(PA).

Composing this direct relative result with the inherited GD calibration gives the requested absolute statement:

    iPRA proves: N does not halt on blank tape <-> Con(PA).

The GD calibration imports the revised AX11H written calibration. Both source archives are preserved under `references/`, with hashes and provenance. The substantial written argument and the unfinished end-to-end Lean formalization are distinguished throughout. This package does not claim to have independently reconstructed or kernel-checked the entire inherited compiler and calibration. Finite execution certificates alone are not offered as proofs of nonhalting.

## Comparison scope

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned commit: `e6a84f8dd2702f5f8c7db3ca53a8cbacb1d89f4f`.

The comparison covers the complete tracked PA tree and the five incoming archives at that commit; the ZFC, DiophantineConsistency and ConciseIPRA trees inform the related-method discussion. Dates in the source packets include both November 14 and November 15. The report uses November 14, 2026 Pacific time.

The fresh scan inventories 29,106 tracked paths, checks 14,898 selected payloads against their Git identities, recognizes 4,437 transition-table occurrences and 1,323 normalized labeled tables, and retains 522 spanning 194-state graph classes plus two nonspanning 194-control encodings. The named ledger contains 85 distinct named principal/supplementary 194-state designs across 93 filed packets and five incoming archives. All 139 historical catalog classes were recovered.

The 522-class census includes auxiliary compositions, rejected candidates and diagnostic tables; it is not a count of 522 established consistency machines. Recognition covers the documented literal text and explicit JSON matrix formats, including recursively inspected ZIPs. It does not execute arbitrary generators or infer tables from prose. See `comparison/comparison_notes.md`, `packet_ledger98.csv` and `named_designs85.csv` for the distinctions and per-design mechanisms.

## Reproduce the main result

Python 3.10 or later with its standard library is sufficient:

```sh
python3 -B reproduce.py
```

This verifies the package manifest, reconstructs all machine artifacts in a temporary directory and compares them byte-for-byte, independently checks the local simulation premises, regenerates the finite Hilbert certificates and emitter inputs, and performs the exact offline novelty comparison against all 524 retained representatives. It does not rerun the longer optimization searches or modify the frozen package. Run with assertions enabled; verification rejects `python -O`.

Individual commands:

```sh
python3 -B verify.py --output /tmp/pa194-regenerated
python3 -B simulate.py machines/PA194GD_SF/machine.tm --steps 58150 --full-tape
python3 -B research/modal_consequents/reproduce.py
python3 -B research/bootstrap/replay.py --max-edits 3 --output /tmp/pa194-bootstrap
python3 -B research/state_reduction/replay.py --output /tmp/pa194-reduction
python3 -B verification/startup_review/replay.py --output /tmp/pa194-startup-review
```

The bootstrap and state-reduction replays also require a GNU-compatible C++17 compiler. Long-search commands and their exact bounds are documented in the corresponding research folders. Runtime depends on the machine. Bounded runs of `simulate.py` do not decide nonhalting.

## What the unsuccessful reduction work establishes

- Fresh joint-return, positive-stuttering and incoming-edge-deletion searches were run on all three children using both coarse reachable windows and regenerated literal source envelopes. All 18 runs returned zero hits. Across the two envelope regimes, pair searches cover 224,652 machine/pair/family instances and 306,289,284 candidate row actions; deletion covers 1,158 controls.
- A broader native 83/190 merge experiment permits one additional non-arithmetic helper row to change. It examined 18,318,203 joint row choices over 256 exterior contexts with an 80-step bound, with no hit.
- Adaptive multi-row blank-bootstrap repair extends the start-74 part of the earlier two-edit experiment. Complete per-budget results and unresolved resource-limit outcomes are recorded under `research/bootstrap/`; these are behavior branches, not a count of all syntactically possible tables. Passing initialization would still require runtime preservation and the correct seed condition.
- Two new consequent-parameterized first axiom heads have explicit primitive-recursive proof translations in both directions. Their certificates have 180, 204, 220 and 382 rows, plus two witness-head translations. Both yield 188-token emitter words. The two 600-second layout searches reached nominal cost 199, not a certified physical machine at or below 194.

Every negative conclusion is restricted to its recorded transformation family and finite bounds. No state-count lower bound is claimed.

## Contents

| Path | Contents |
|---|---|
| `report/` | Main PDF, complete TeX source, generated data tables, build scripts |
| `machines/` | Three dense/native tables, selector intermediates, label maps, exact certificates |
| `inputs/` | Exact GD/GDH/GDHS parent tables and inherited startup receipts |
| `comparison/` | Full census, 98-packet and 85-design ledgers, 524 representatives, novelty witnesses and code |
| `research/bootstrap/` | Adaptive multi-row repair source, inputs, logs, bounded-result summary and replay |
| `research/state_reduction/` | Fresh quotient/deletion/helper/rotation experiments, envelopes, logs and portable replay |
| `research/modal_consequents/` | New logical heads, finite proof generators/checkers, emitters and layout searches |
| `verification/` | Independent local-proof review and controlled bootstrap-search tests |
| `references/` | Preserved GD and revised AX11H calibration archives and selected source excerpts |
| `licenses/` | Inherited ProveIt, James Chang and Wade attributions |
| `RESULTS.json` | Machine-readable summary and exact claim boundaries |
| `MANIFEST.json` | SHA-256 identities of delivered files |

Build the report with `python3 -B report/build.py`, or run `pdflatex -interaction=nonstopmode -halt-on-error report.tex` twice from `report/` on a normal TeX installation. The supplied build helper handles the missing-format configuration encountered in the research environment. No Lean installation is required to replay the finite checks; no new Lean completion is asserted.
