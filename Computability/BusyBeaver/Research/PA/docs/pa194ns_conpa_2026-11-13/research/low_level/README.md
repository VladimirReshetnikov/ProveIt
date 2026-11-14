# Bounded state-reduction searches for PA194NS

No machine below 194 states was obtained by these searches. The result is a
finite search record, not a state-count lower bound.

The frozen inputs are the PA194NS native transition table and its complete
3650-site source graph. There are 4750 primitive outcomes. The generic
symbolic contracts, followed by literal startup, yield 16293 conservative
radius-five tape windows for 171 non-arithmetic-box controls. The 23 box
controls retain the broader all-tape abstract-reachability windows in the
C++ searches. Unknown register-file prefixes are deliberately overapproximated
by arbitrary bits. Affine-run correlations are discarded, never assumed.

Three searches were completed:

| Search | Context radius | Maximum detour | Successful candidates |
| --- | ---: | ---: | ---: |
| Merge two controls, with joins at bounded future original configurations | 4 | 100 | 0 |
| Same merge with source/startup windows | 5 | 150 | 0 |
| Delete one control by rewriting every incoming row, with future joins | 5 | 150 | 0 |

The first search uses all-tape abstract reachability from the native start
control 74. A radius is measured in cells on each side of the head. The
step bound applies to each examined local segment. The candidate first
transition may write either symbol, move either direction, and target any
remaining control. The frozen C++ programs also impose their documented
avoidance conditions to keep changed-row dependencies sound. Thus a zero
result excludes only those particular finite search classes.

## Reproduction

Python 3.10+ and a C++17 compiler named `g++` suffice. No network or solver
is needed; retain Python assertions. A standard replay writes its outputs
in a fresh temporary directory:

    python3 replay.py

Rebuild the context file from all universal symbolic contracts and the exact
57768-transition startup as well:

    python3 replay.py --derive-contexts

An optional `--output /absolute/directory` selects the output directory.
The scripts leave the delivered inputs unchanged. The longer replay checks
byte equality of the newly generated context file with the frozen one.

The inherited symbolic runtime calls its unchanged arithmetic-box lemmas;
these are used only to derive conservative search inputs. The authoritative
independent physical checker of PA194NS rederives those lemmas from the
literal table. This search package does not itself add a kernel proof.

## Scanner experiment

Native controls 2, 3, 5, 9, 15, 23, 34 detect a run of seven zero cells before
reversing through control 75. Simply deleting 34 and redirecting targets 34
to 75 creates a 193-control table, but fails the very first universal source
contract: source site 0, the zero branch of logical register 5 (physical7).
That source address is `000000`. The prematurely reversing scan can enter
its middle with the register file still marked. `replay.py` rechecks this
specific failure and writes `scanner-rejection.json`.

This is rejection of that proposed simulation-preserving optimization. It
is not an assertion that the modified table's entire blank execution has
been characterized, and it is not a rejection of every possible redesign
of the scanner or source encoding.

## Provenance

`action_merge_future.cpp` and `eliminate.cpp` are copied byte for byte from
`Computability/BusyBeaver/Research/PA/docs/pa194C_conpa_2026-11-13_2/search/physical`
in ProveIt commit `1e407ae841e4666f932777fad977ba784ebbcfd5`.
`reference/symbolic_runtime.py` is copied from the incoming PA194R packet's
construction runtime at that same revision. License notices are retained
beside it. `replay.py`, the PA194NS inputs, the generated windows, and these
new search results belong to the present follow-up.
