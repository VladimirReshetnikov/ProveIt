# Searches from the fresh 68-reader / 8-fold PA194 frontier

The freshly added `pa194_conpa_2026-11-13 (2).zip` contains a different
194-state reader allocation: 134 fixed controls, 68 raw readers, and eight
simultaneously compatible folds. The previous starting point had 67 raw
readers and seven folds. Both therefore leave 60 effective readers.

This directory records additional heuristic searches from the new allocation,
under both the published S controller and the cached C controller. A target
requires at most 59 effective readers with zero screening penalty, which
would give at most 193 working states before complete verification. Numerical
hits would still require source-CFG equality, complete literal execution
checks, and exact blank-tape initialization. The observed results are in
`results.json`. Both runs were interrupted before their 600-second budgets
finished. Their last complete progress records are D: 11,512,000 proposals
at 571.320 seconds, and E: 11,484,000 at 571.352 seconds. Neither log has
a DONE record or a target-hit record; both retain a best score of 60. These
are partial recorded counts, not claims of completed 600-second runs. The
searches were not resumed. These searches establish no state lower bound and do not
prove every attempted reassociation semantically invalid.

## Input binding

`new194.grammar.json`, `new194.folds.json`, and
`new194.unfolded202.native.tm` are byte-for-byte copies from the new archive.
`PROVENANCE.json` binds the archive and repository revision.
`build_inputs.py` translates the grammar to postorder syntax records and
copies its 134 fixed controls into `start194altS.txt`. It creates
`start194altC.txt` by changing exactly the six cached-controller transitions
already justified in this package's principal construction. It does not
rename parameters or alter the 190-token emitter word.

The unchanged screen reports **68 raw readers, eight compatible folds,
60 effective readers** for each input. The search itself reports an initial
score of **60**, so neither starting point incurs a scanner penalty.
`checkS.audit` and `checkC.audit` record the screen's component counts.

`check_inputs.py` independently binds the encoded fixed rows to the raw
compiler output. It checks the complete resolved source CFG against the
published S/C references, all 32 two-cell fold cases, every symbolic source
contract, graph reachability, and equality of the entire finite-support
blank startup tape. These symbolic contracts use the inherited arithmetic
block lemmas. This starting-point audit does not independently rederive those
lemmas, validate search-generated grammars, or claim a new kernel theorem.

The C composition is included only as a reproducible search input. The
principal deliverable remains PA194C from the 67-reader / 7-fold allocation.
The dense hashes in `input_validation.json` use the builder's breadth-first
numbering, so they differ from the new packet's sorted-state numbering even
when the native table is identical.

## Reproduction

Run from this directory, with Python 3.10+ and a C++17 compiler:

```sh
python3 -B build_inputs.py
python3 -B check_inputs.py ../../../construction
g++ -O3 -std=c++17 screen.cpp -o screen
g++ -O3 -std=c++17 search193_occ.cpp -o search193_occ
./screen start194altS.txt checkS 1 1 compatible
./screen start194altC.txt checkC 1 1 compatible
./search193_occ start194altS.txt leaf_attrs.txt runD 600 2026111408
./search193_occ start194altC.txt leaf_attrs.txt runE 600 2026111409
```

`screen.cpp`, `search193_occ.cpp`, and `leaf_attrs.txt` are unchanged copies
from the parent search directory. Their hashes are recorded. The two
planned 600-second runs were launched concurrently and interrupted before
completion. Counts include repeated and
no-op proposals; they do not count distinct machines. Runtime-limited
proposal counts may differ on another computer.

## Additional local checks

The two literal search input tables are `pa194altS.native.tm` and
`pa194altC.native.tm`. The same local-detour and incoming-edge deletion
searches supplied in `../../local/` were also run on both tables. The saved
logs and JSONL outputs cover radius four / 120 steps and radius eight /
200 steps, starting from arbitrary-tape local closure. Each merge run
examines 194 controls; each deletion run examines 172 eligible controls.
An empty JSONL file means that no candidate was returned under that
particular bounded criterion.

```sh
g++ -O3 -std=c++17 action_merge_all.cpp -o action_merge_all
g++ -O3 -std=c++17 incoming_eliminate.cpp -o incoming_eliminate
./action_merge_all pa194altS.native.tm 4 120
./action_merge_all pa194altC.native.tm 4 120
./incoming_eliminate pa194altS.native.tm 4 120
./incoming_eliminate pa194altC.native.tm 4 120
./action_merge_all pa194altS.native.tm 8 200
./action_merge_all pa194altC.native.tm 8 200
./incoming_eliminate pa194altS.native.tm 8 200
./incoming_eliminate pa194altC.native.tm 8 200
```

No compiled binaries or unverified intermediate pool grammars are retained.
Original licenses are preserved under `../../../construction/licenses/`.
