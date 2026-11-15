# Completed physical-reduction searches and a scanner counterexample

**No sub-194 consistency machine is established here.** This supplement records
four completed investigations, with their exact scopes and portable inputs.
They support the report's account of the search effort; none is a global state
lower bound. The separate `helper194` construction supplies a valid new
same-count physical companion.

`search_summary.json` is the compact machine-readable result. Source pins and
attribution are in `PROVENANCE.json`; input hashes are in `input_sha256.json`.
All scripts use Python's standard library, except the bootstrap search, which
also requires a C++17 compiler. Keep Python assertions enabled; do not use `-O`.

## 1. Previously protected register-interface rows

The ordinary searches protect all register-box controls. We additionally
screened the read-0 rows of native controls 3, 16 and 113, keeping their read-1
rows fixed. For each retained control, each of 170 eligible non-box controls
was deleted into it and every possible binary write, direction and remaining
state/halt destination was tried for the retained read-0 row: **395,760**
variants altogether. The source executor uses all **4,780** primary source
outcomes. No candidate survived the bounded symbolic checks.

The screen begins at the first affected state in each known source trace,
which avoids repeating the unchanged prefix. Its bound is 1,024 symbolic
updates per suffix. Arithmetic boxes and arbitrary unary runs can represent
unbounded literal time; this is not a small-register test. A failed bounded
symbolic replay is nevertheless not a proof that no longer equivalent path
exists. No survivor was promoted to a machine equivalence claim.

Optional full replay, from this directory:

```
python3 search_box_edges.py
```

It writes `fresh_box_edge_results.json`. Recorded output is preserved under
`recorded/box_edge_results.json`. The observed run took about 392 seconds;
timing is incidental, while the enumeration count is reproducible.

## 2. Inductive local-window shortcut closure

A radius-six local abstraction begins with the all-zero window in native
control 74. A head move admits both possibilities for the newly exposed
exterior bit. Its least closed set therefore overapproximates every literal
blank computation, by an elementary induction. The primary table gives
**267,827** abstract state/window contexts.

For every state/read case, we intersect actions obtainable by an old trace
of at most 127 transitions inside the window, leaving the whole window
unchanged except the current cell and making one net head move. This finds
exactly the already-known three-to-one shortcuts

- `26/read1 -> 1 R 91`;
- `101/read0 -> 0 R 17`.

No simultaneous choice of the admitted actions deletes a working control.
Applying both shortcuts and recomputing the abstraction gives **267,187**
contexts and no additional shortcut in this template.

```
python3 search_inductive_shortcuts.py --radius 6 --fuel 127 --output /tmp/primary-shortcuts.json
python3 search_inductive_shortcuts.py --radius 6 --fuel 127 --input inputs/primary_fast.native.tm --output /tmp/fast-shortcuts.json
```

Each observed run took about 11 seconds. The exact finite representation is a
restriction, not a theorem about all physical encodings or all machines.

## 3. Combined edits of the known Runtime193 core

The inherited runtime-only 193-state table is **not a valid blank-start
consistency machine**. It shares the register marker with a history fold and
breaks its initializer. We tried pairs and triples from the 346 inherited,
corrected source-context-neutral row proposals. These proposals are search
inputs; their simultaneous combinations are not assumed to remain neutral.

A guide run discards an edit whose row is not encountered before the stated
bounds. The replay examines 1,099 effective distinct-row pairs and 19,424
effective distinct-row triples from blank start 74. A target can be any
canonical source frame at sites 25--44, with gap at least 48, arbitrary
register values, at least ten complete register blocks, and blank exterior.
No target is reached.

| Replay | Trials | Candidate transitions | Fuel bound | Outward ray | Range bound |
|---|---:|---:|---:|---:|---:|
| Two edits | 1,099 | 22,908,918 | 114 | 982 | 3 |
| Three edits | 19,424 | 879,569,779 | 4,385 | 14,866 | 173 |

Each candidate has a 200,000-transition bound and absolute head-displacement
bound 1,500. The transition totals exclude guide runs. Outward-ray detection
uses a literal self-loop on a blank cell beyond all cells ever written 1,
with movement farther outward, so that classification has a direct induction.
The fuel and range outcomes are inconclusive; no permanent failure is inferred
from them. No candidate halted in these recorded screens.

```
c++ -std=c++17 -O1 bootstrap_pairs.cpp -o /tmp/pa-bootstrap-pairs
/tmp/pa-bootstrap-pairs inputs triples
```

The exact observed output is in `recorded/bootstrap_pairs.log`. Inputs are
fixed and require no repository checkout or network access.

## 4. A literal counterexample to deleting the seventh scanner state

The tempting edit deletes native control 34 and changes row 23/read0 to
`0 L 75`. It is already wrong on the actual initialized source instruction,
with logical candidate counter 2 and the selected register zero. The baseline
blank machine reaches the clean frame at site 25 after 58,154 transitions.
From that frame, parent and shortened tables reach the same complete tape,
control 23 and head -1 after 223 and 221 transitions respectively.

The parent scanner then returns in 19 steps to dispatch 84 at head -2, while
the shortened scanner returns in 2 steps to dispatch 84 at head -1. Thus the
proposed scanner replacement does not preserve its required return coordinate.
This is a finite, concrete counterexample to that drop-in contract, not a
global assertion about halting of the altered machine.

```
python3 check_scanner_counterexample.py --output /tmp/scanner-counterexample.json
```

The replay first checks the complete 58,154-step baseline initialization and
then the two exact scanner traces. The full tapes are recorded in
`recorded/scanner_counterexample.json`.

## Provenance and interpretation

The frozen primary table and symbolic executor come from the primary PA194
packet. Runtime193 and the neutral-row proposals come from the earlier
`pa_sub194_research_2026-11-13` packet. Their precise repository paths and the
current pinned commit are in `PROVENANCE.json`. Original ProveIt, James Chang
and Andrew James Wade licenses are retained under `licenses/`.

Only the completed, correctly scoped screens are included. No global
impossibility result, new sub-194 machine, or new Lean consistency endpoint is
claimed by this supplement.
