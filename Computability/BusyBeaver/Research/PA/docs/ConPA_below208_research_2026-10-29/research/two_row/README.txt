TWO-ROW STATE-IDENTIFICATION SCREEN

This is a candidate-discovery program, not a nonhalting checker or a proof of
minimality. It tests each unordered state pair, including start-state pairs
(state 0 is retained), allows both outgoing keeper rows to change, and projects
all removed-state targets to the keeper. New actions choose a binary write,
left/right move, and any retained working target. Halt is not a synthesized
target. A new positive block must match one old step with equal entire sampled
tape, equal head coordinate, and projected control state.

Run from anywhere; use Python 3.10+ and a C++17 compiler:

  python3 run.py --class control --output /tmp/u208-control
  python3 run.py --class A --output /tmp/u208-pairs-A
  python3 run.py --class B --output /tmp/u208-pairs-B

Defaults: history depth 12, at most 71 new transitions per old step, three
deterministic random completions for each cylinder/read-bit pair. The control
uses U209 and must recover exactly delete 211/keep 172 with actions 0 L 217,1 R 184.
Each U208 run checks 21,528 unordered pairs and 35,650,368 partial actions.
The retained split logs cover 21,321 noninitial pairs plus 207 start-state pairs.
Both classes had zero survivors. The newer one-process driver includes the
same pairs and uses the same partial-hole pruning and complete survivor cross
product. It emits a complete log and a machine-readable receipt.

The history construction starts from every working state with an arbitrary
tape, takes exact forward images 12 times, and injects state 0 with arbitrary tape
at every iteration. Thus it covers every actually reachable old configuration,
including initial prefixes shorter than 12. Separate cylinders retain conditional
bit correlations. Subsumption removes only cylinders covered by a weaker one.

The partial-row screen permits an unresolved second keeper row to rescue a
case: it rejects only if the already assigned row fails before the other row
is encountered. All surviving pairs of complete rows are then checked. Random
completions are used only to REJECT; no candidate would be accepted without an
independent exact symbolic proof. Even these failures do not establish actual
program reachability of their witnesses, and the block relation and bound are
restricted. There is no general 207-state impossibility claim.

An explicit state->list-of-cell-dictionaries JSON file can replace the history
generator with --contexts; this supports the separately harvested restricted
source contexts. That file's derivation is a separate research obligation.

The archived strongest source-conditioned run can be repeated from the release
root with this command (gzip input is supported directly):

  python3 research/two_row/run.py --class A \
    --contexts research/source_contexts/data/restricted_alias208_r4_h12.contexts.json.gz \
    --output /tmp/conpa-source-pairs

Its 169 retained checkpoint logs cover all 21,528 pairs and report zero
survivors. restricted_source_summary.json gives their summed census. The
one-process replay uses the same cases and boundary relation; chunking changes
only how the completed search was checkpointed during the research session.

Attribution: the disjunctive forward-image construction follows the supplied
Entry Context packet's discover_folds.py, retained in baseline/. The two-row
partial-hole synthesis and all-state extension were implemented for this
dossier. Original machine/source notices are retained in baseline/snapshots.
