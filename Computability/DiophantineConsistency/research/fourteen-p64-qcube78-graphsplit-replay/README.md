# Guarded replay of the 78 actual-zero split

On 2026-11-04 [`run.py`](run.py) independently reran the existing
`P64QCube78GraphSplit.first_eq_one` source. Lean exited 0 in 7.217 seconds;
the retained [output](observations/attempt01/compile.log) has precisely the
expected `[propext, Classical.choice, Quot.sound]` axiom report and no
warning, error or `sorryAx`. The [receipt](observations/attempt01/result.json)
records the actual command, exit, log hash and direct input guards. Its
output object SHA-256 is
`76da5f69b14d211994c5ccc12e9e9de9d5d3b585b002149bca4922d7ca536150`,
byte-identical to the original graph-split object used by the separately
replayed 78 positive-zero equivalence.

The runner checked source, executable and two direct object hashes and their
first existing search-path locations before and after the run, refused an
occupied Lean slot and existing output paths, and recorded a 300-second
bound. This is a second execution against the same captured providers, not
a fresh source rebuild or a full audit of project, package, dynamic and
search-path ancestry. It does not independently establish the zero
equivalence, iPRA endpoint, or file/PDF binding.

The runner and result use fixed temporary paths and refuse to overwrite
existing files; a new run needs fresh output and observation paths in a copy
of the runner. SHA-256: `run.py`
`cc6567b3a14a64435a9a5024498df62ea56c1d028ef92f5a81d1f24654382c1e`;
`result.json` `4c1d3b25b504228faabf20b7eb15b2dda4925c99c20dc424a3fdb3928bf56a5f`;
`compile.log` `89fb364a4751e93ea82957cf47122c06c8cdc51e52b46f68a837339106cd7529`.
