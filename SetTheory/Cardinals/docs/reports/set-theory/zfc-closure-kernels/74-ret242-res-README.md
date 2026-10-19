# Optional exploratory reruns

Run the commands below from the extracted archive's top-level directory. They
require Python 3 and its standard library. The main archive README describes
the verification of the selected 242-state construction. The scripts here
document the bounded searches and diagnostics that informed it.

## Scanner contraction diagnostic

```bash
python -B research/scanner_probe.py --help
python -B research/scanner_probe.py --output research/rerun/scanner-probe.json
```

The defaults resolve relative to the extracted archive, independently of the
current working directory: the input table is
`reference/combined243/zfc_combined243_old.tm`, the unchanged logical source is
`machine/sites_logical.json`, and the helper is the unmodified bundled
`scanner_support/check_combined243_literal.py`. The runner checks the exact table
and source SHA256 values. The support directory's NOTICE records the helper's
pinned source and hash. No repository checkout or downloaded dependency is needed.

This diagnostic replays one deterministic finite register/spare fixture for
each of the 8,390 source/guard cases. At visits to inherited row `41/0`, it records
five adjacent tape bits and counts contexts that fail the three-zero premise
of a proposed scanner contraction. Each fixture has a 20,000-transition limit,
adjustable with `--step-limit`. It checks the exact baseline source-instruction
endpoint before accepting the fixture.

The stored `scanner-probe.json` is the original executed diagnostic. A rerun
writes a new file; its elapsed time will differ, and the portable runner also
records the input/helper hashes and limit. Failing the sufficient local premise
does not establish that every possible scanner contraction is incorrect.

## Local state-reduction searches

The scripts in `local-search/` resolve their default input `base243.tm` beside
the scripts. `LOCAL_RESULTS` selects an output directory without changing the
input. `LOCAL_TABLE` selects another table explicitly. Table overrides must use
the **inherited labels**, with start 95 and halt 254; the search model contains
those labels as fixed parameters.

The direct-redirection search originally used radius three, then radius five,
with a maximum symbolic trail length of 12 transitions:

```bash
LOCAL_RESULTS="$PWD/research/rerun/direct-r3" python -B research/local-search/search_folds.py 3
LOCAL_RESULTS="$PWD/research/rerun/direct-r5" python -B research/local-search/search_folds.py 5
```

The search for independent replacements of the incoming rows of a deleted
state uses radius four and trails of at most 14 transitions:

```bash
LOCAL_RESULTS="$PWD/research/rerun/incoming-r4" python -B research/local-search/search_incoming.py 4
```

The successful hybrid-absorption search is reproduced by:

```bash
LOCAL_RESULTS="$PWD/research/rerun/combined243-hybrid" python -B research/local-search/search_compensation.py 4 all
```

The corresponding search on the selected 242-state result is:

```bash
LOCAL_TABLE="$PWD/research/local-search/zfc_return242_old.tm" LOCAL_RESULTS="$PWD/research/rerun/return242-hybrid" python -B research/local-search/search_compensation.py 4 all
```

The positional `4` is the tape-window radius: positions -4 through +4, or nine
bits. The `all` mode considers each possible deleted working state except the
start, each retained absorber, and three choices of which absorber rows to take
from the deleted state. It checks the redirected entries and searches a limited
family of incoming-row repairs, with at most three failing incoming entries.
Candidate trajectories must rejoin an identical retained checkpoint with the
same head and entire tape within the symbolic trail limit. Reading beyond the
known window prevents acceptance of that attempted local proof. These are
bounded searches of particular transformations, not an enumeration of all
smaller Turing machines.

The combined243 run considered 175,692 hybrid proposals over 29,053 abstract
reachable state/window pairs. Its six labelled hits represent three machine
isomorphism classes, borrowing state 27's formerly inadmissible one branch for
old state 15, 50, or 171. The selected state-15 reduction has its own complete
ordinary proof and independent local verifier. The follow-up run on 242 states
considered 174,243 proposals over 29,049 abstract state/window pairs and found no
further fold within this family. These counts and the recorded alternatives
are in `local-search/search-summary.json`.

Each complete hybrid run took several minutes in the research environment;
runtime depends on the machine. The results include bounded-search failures,
which do not prove minimality or rule out a 241-state construction.

The copied standalone local proof checker can also be run directly:

```bash
python -B research/local-search/verify_return242.py
```

It checks the exact pinned tables, complete finite invariant inventory, the
two universal finite block identities, all ordinary-row conditions, and the
prescribed full blank bootstrap. It rewrites its adjacent certificate JSON.
This proof checker is independent of the exploratory search heuristics.
