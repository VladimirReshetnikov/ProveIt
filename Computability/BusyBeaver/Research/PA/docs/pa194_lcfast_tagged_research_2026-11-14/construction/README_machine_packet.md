# Two new 194-state compositions

This self-contained supplement constructs **PA194LCAX11GHF** and **PA194LCAX11GHSF**. It combines the incoming GH/GHS source programs, loop-continuation routing, and the two guarded decoder shortcuts. The source instruction graphs are identical to the corresponding parents. Exactly five native transition rows differ. Both tables have 194 working states, a separate halt state, and two symbols; all working states are graph-reachable from start.

| Candidate | Source instructions | Branch contracts | Exact blank startup | Independent symbolic operations |
|---|---:|---:|---:|---:|
| PA194LCAX11GHF | 3,671 | 4,778 | 57,870 | 1,105,240 |
| PA194LCAX11GHSF | 3,668 | 4,774 | 57,712 | 1,109,186 |

Dense tables are `machines/<name>/machine.tm`. Dense start is 0, blank symbol is 0, and halt is 194. Each line is `state read write direction next`, with directions L/R. Native tables use start 74 and halt 254; `labels.json` gives the dense-to-native conjugacy, including halt as its final entry. The raw native files retain the unfolded reader controls before the contextual folds and the final fast shortcuts.

## Exact files

- GH dense SHA-256: `01c1b37ac3bbc51b2dfef22b8e42a6b3713ed720350269f819d82793e3f01bce`.
- GHS dense SHA-256: `6d03507fcc85825f81f7db5d02b0cb60e48f87c53be3dd0e4a8888d4922517a9`.
- `proof/relative_proof.tex` gives the exact transformations, ordinary iPRA relative proof, bounded halt-witness extraction, and common explicit bound `Theta(t)=13t^2+715t+58624`.
- `verification/independent/results/` contains complete newly replayed symbolic literal contracts and whole blank startup tapes. This checker uses no arithmetic-box oracle and imports no builder.
- `verification/parent_recorded/` retains the supplied parent certificates; their separate provenance is identified in `verification/clock_receipt.json`.
- `build_receipt.json` and `construction.log` record deterministic construction, simultaneous fold checks, source graph identity, and construction-side symbolic contracts.
- `context_fold_search.json` records a bounded unsuccessful search for an additional state fold. It is not a lower-bound result.

## Reproduce without replacing the frozen deliverables

Python 3.10 or later and the standard library suffice. Assertions must remain enabled; do not use `python -O`.

```sh
python3 reproduce.py
```

The wrapper copies the packet into a temporary directory, rebuilds both tables, replays all source contracts and all literal contracts, checks the exact startups, checks the duration coefficient envelope, and compares the generated files with the frozen artifacts. It reports PASS only after byte-for-byte comparison. It leaves the supplied outputs untouched.

For a shorter deterministic table build and construction-side replay:

```sh
python3 reproduce.py --construction-only
```

To inspect only the frozen coefficient audit:

```sh
python3 verification/check_clocks.py
```

The independent symbolic engine is an executable mathematical checker, not a proof-assistant kernel. The full ordinary relative argument is in the TeX file. The `raw_controls` receipt means all unfolded fixed plus reader controls, not merely the fixed subsystem.

## PA calibration dependency

The new results establish relative equivalence with the supplied GH and GHS parents. The parent GH/GHS reports rely on the AX11H numerical refutation calculus and its incoming written PA calibration. If that parent iPRA calibration is established, the relative theorem transfers `Nonhalt <-> Con(PA)` to each new table. This packet does not fill the incomplete end-to-end Lean proof and does not present finite execution as an absolute consistency proof. The parent absolute proof dependencies are the incoming GH/GHS research report and the supplied AX11H arithmetic-calibration manuscript identified by the accompanying overall archive report.

The two compositions are structurally distinct from the supplied corpus under the separately retained census comparison. The component transformations were already supplied; their combined tables and exact verification are new. See `NOTICE.txt` and the preserved upstream `licenses/` directory.
