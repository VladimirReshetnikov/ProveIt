QNS5 THREE-WAY CONTROL-SHARING SCREEN

RESULT AND PURPOSE

No replacement pair was found in this bounded screen. This is a small,
reproducible negative experiment, not a lower bound on PA consistency machines
and not a proof that a more general sharing construction cannot work.

QNS5 combines Q quantifier-head exchange, no-push MP, the symmetric comparator,
and radix five. Its frozen raw table has 203 controls. Seven existing AX folds
leave 196. This experiment attempts to replace controls 41, 99, and 330 by one
shared control, 99, which would leave 194 controls. Every other row is fixed
after the seven AX folds and the two target redirections.

The helper names are specific to this QNS5 table:
  330 is the symmetric-comparator helper:
      330/0 = 0 R 63, 330/1 = 1 L 73.
  331 is the radix multiplier helper, which remains present:
      331/0 = 0 R 61, 331/1 = 1 R 99.
The QN5 construction elsewhere uses 330 for its multiplier helper. That naming
does not apply to the table in this directory.

QUICK REPRODUCTION

From this directory, run with Python 3 (standard library only):

  python3 -B search.py --output /absolute/fresh/output-directory

The output directory is optional; the default is ./replay. There is no network
access, compiler import, working-tree dependency, or proof assistant involved.
Do not use Python -O: assertions check the identities and expected results.
The file hash manifest is checked before the screen runs.

The portable rerun reproduces the original results exactly, disregarding time:
  current-zero cases: 211
  current-one cases:  106
  surviving zero-row actions: 0 L 99, 1 L 99, 1 L 190
  surviving one-row actions:  0 L 99, 1 L 99
  simultaneous pairs checked: 6
  successful simultaneous pairs: 0

PRECISE LIMITED SCOPE

The fixed sample records eight cells to the left of the current head and three
cells starting at that head. These form an 11-cell window, indexed 0 through
10, with initial head index 8. Short extracted sides are padded with zero on
the exterior side. The screen requires each of the 317 contexts belonging to
41, 99, and 330 to simulate that original control's single transition, including
the exact resulting control, head position, and all 11 tape cells. Targets 41
and 330 are redirected to 99 in both the tested and expected configurations.
The 56 recorded contexts for 331 are preserved as provenance but are not tested
as entries to the shared control.

For each replacement row, the search enumerates both writes, both directions,
and all 194 remaining working controls as targets: 776 actions per row. The
halting control and new controls are not available as replacement targets.
In the preliminary one-row screen, encountering the other unspecified row is
inconclusive and retains the action. The final six pairs specify both rows and
must succeed on every case. All other transitions remain fixed.

The original loop executes at most 50 transition iterations. It checks exact
endpoint equality at the start of iterations 1 through 49; an endpoint reached
only after transition 50 is not accepted. search.py preserves this boundary
exactly rather than silently changing the original experiment. A path that
leaves the 11-cell window, reaches a missing row, or exceeds that bounded loop
is rejected. Thus a valid construction using a larger window, a longer local
simulation, different endpoint synchronization, different other rows, or a
different source representation could be missed.

The contexts are a finite sample extracted from a symbolic source-contract
execution, not an asserted enumeration of every concrete runtime context.
A positive hit would still need the full source, startup, and correctness
obligations. The negative result concerns only the frozen sample and bounded
replacement scheme described above.

SOURCE AND CONTEXT PROVENANCE

data/ contains the exact frozen QNS5raw raw table, source nodes, source sites,
instruction CFG, seven AX folds, Q grammar, and extracted context JSON. The
original paths and SHA256 identities are recorded in PROVENANCE.json. They are
provenance labels, not required filesystem locations. The repository comparison
was pinned to ProveIt commit 2337ce611a26e308697ccbddb2a1636f989f01c3.

The original root_research/threeway_contexts.py observer ran on the unfolded
203-control raw table, during all source contracts generated from the frozen
QNS5 source. Its successful validation receipt was:
  contracts 4812, max_steps 470, total_steps 1494476.
Those counts are the symbolic executor's units, including its normalizations
and arithmetic-block summaries; they are not a literal blank-run step count.

The observer collected states 41, 99, 330, and 331 only when its onl flag was
false. It extracted known bit prefixes of widths eight and three, reversed the
left prefix to physical order, and deduplicated pairs. The resulting counts
are 163, 150, 4, and 56 respectively. The supplied frozen sample has no unknown
bits in any context used by the screen. The original context-generation run
is inherited evidence and was not redundantly rerun to make this package.

OPTIONAL CONTEXT REGENERATION

The final archive places this directory at research/threeway and the compiler
at construction/vendor. In that layout the following regenerates the contexts
and checks exact source, receipt, and context equality:

  python3 -B regenerate_contexts.py --output /absolute/fresh/output-directory

For another layout, specify --construction /path/to/construction. This optional
command imports only compiler.py and symbolic_runtime.py from that directory,
checks their frozen hashes, and uses the source and raw table in data/. It never
imports search_compose. A cheaper structural check, without contract execution,
is available as:

  python3 -B regenerate_contexts.py --source-only --construction /path/to/construction

The source-only mode was run successfully while packaging; full regeneration
is optional because the exact original context JSON and original validation
receipt are already preserved.

FILES AND ATTRIBUTION

search.py is the portable bounded screen. regenerate_contexts.py is the optional
context collector. recorded/ retains the original result, portable replay, and
structural binding receipt. PROVENANCE.json and MANIFEST.json record identities.
The original ProveIt and James Chang license texts are retained. The inherited
symbolic executor's verification boundary remains unchanged: this package does
not supply a Lean or Rocq theorem, and supplies no new PA consistency machine.
