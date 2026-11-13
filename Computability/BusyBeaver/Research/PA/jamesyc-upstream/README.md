# James Chang's PA196 and PA209 snapshots

These directories preserve complete, unmodified Git trees from
[`jamesyc/BusyBeaver`](https://github.com/jamesyc/BusyBeaver), including their
standalone Lean projects, machine tables, papers, scripts, dependencies, and
license notices. The upstream root license is MIT; bundled dependencies retain
their own notices in each snapshot. These are research source snapshots, not
integrations into the main ProveIt Lake build.

| Directory | Upstream source | Commit | Author date |
| --- | --- | --- | --- |
| `pa196/` | [PA196 at upstream main](https://github.com/jamesyc/BusyBeaver/tree/407cdc356f6b586635e71ac92be394255f4bfea4/PA196) | `407cdc356f6b586635e71ac92be394255f4bfea4` | 2026-11-12 |
| `pa209/` | [Earlier PA209 repository](https://github.com/jamesyc/BusyBeaver/tree/69d98241a721ead20b4f0b17df9062950b40fbfe) | `69d98241a721ead20b4f0b17df9062950b40fbfe` | 2026-11-11 |

The snapshots were exported with `git archive` from these commits. On import,
every tracked blob and executable bit was checked against its upstream Git
tree: 2,141 files in `pa196/` and 2,211 in `pa209/`, with no mismatches or
extra files. Running each snapshot's `bash scripts/check.sh` passed the
upstream source and machine checks. These checks are not a Lean build; the
upstream `--full` check was not run during import.

The literal table `pa196/data/pa196.tm` has 196 working states, 392 rows, and
separate halt label 196; its SHA-256 is
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
The table `pa209/data/pa209.tm` has 209 working states, 418 rows, and separate
halt label 215; its SHA-256 is
`0610d978675320f0b4b1ef34619dcd3daa5912632d7037e200dfcc70954fea51`.
Each working state has one row for each binary symbol. Both machines start
in state 0 on an all-zero tape.

The upstream PA196 result states that PA proves the implication from the
literal machine's nonhalting to `Con(PA)`, and that nonhalting is proved in
the Lean metatheory; see `pa196/docs/result.md` and `pa196/paper/pa196.tex`.
That stated implication alone does not establish that PA proves the converse
`Con(PA) → nonhalting`. In particular, the source and table checks above do
not verify an end-to-end PA-provable consistency biconditional. Consult the
upstream proof, assumptions, and reproduction instructions for their exact
scope.
