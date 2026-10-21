# Bounded physical searches for 214 states

The searches in this folder did not produce a 214-state candidate. They are
included as reproducible negative research, with explicit search scopes.
`summary.json` gives the counts and `evidence/` contains the original receipts.
`provenance.json` pins the copied inputs and inherited helpers to their origins.
No network or repository checkout is needed to rerun them.

## Finite local fold certificates

The Python search examines every unordered pair of working states. It redirects
references to the removed state to the retained state, and tries each choice
of the original two rows for the merged state's read-zero and read-one actions.
When one branch already agrees under the state map, it also tries every possible
write symbol, head direction and remaining target for the other branch.

The discovery filter seeks positive common endpoints in a finite window over an
inductively computed context set. Radius 7 means a 15-cell window. Both the old
and new local paths have a 97-step limit. A filter failure is not a semantic
counterexample: a valid equivalence may require a larger window, longer join,
stronger invariant or another state relation. Had a candidate passed the filter,
the separate inherited checker would have been invoked on every context. None
did, so no successful all-tape equivalence certificate is claimed here.

| Seed | Radius | Fuel | Specifications | Hits |
|---|---:|---:|---:|---:|
| Accepted K215 | 5 | 97 | 316,292 | 0 |
| Accepted K215 | 7 | 97 | 316,292 | 0 |
| Short-transfer append-one precursor | 7 | 97 | 309,444 | 0 |

From this directory:

```sh
python3 -B search_folds.py --table inputs/k215.native.tm --radius 7 --output rerun-k215
python3 -B search_folds.py --table inputs/short-transfer.append-one.native.tm --radius 7 --output rerun-short
```

Each command emits `<output>/result.json` and prints progress. The original
radius-7 domain sizes printed by the search were 970,607 and 972,533 contexts,
respectively. The search code uses bundled copies of the pinned repository's
`check_joint_fold.py` and `search_v3.py`. Only path resolution and parent output
directory creation were changed in the coordinating script.

## Concrete primitive quotient screening

The inherited C++ program first checks all 6,151 guarded primitive entries of
the short-transfer append-one source at one small arithmetic fixture. All
primary registers are zero, except that the selected register is one for a
positive decrement. The gap is zero and the spare list is `[0]`. Baseline
execution succeeds for every case.

It then tests every pair of non-dispatcher states and all four choices of which
member supplies each branch of the merged state. There are
`4 * binomial(214,2) = 91,164` candidates and zero survivors. The baseline limit
is 10,000 transitions per case; the modified-table limit is three times that
case's observed baseline duration plus 100. Tape storage is a fixed 512-cell
window. Exceeding a limit rejects a candidate in this screen, and is not a proof
that its unbounded execution is wrong.

Compile with GNU C++ (the implementation uses libstdc++ bitset extensions):

```sh
python3 -B make_cases.py --out cases.txt
g++ -O2 -std=c++17 direct_merge.cpp -o direct_merge
./direct_merge inputs/short-transfer.append-one.native.tm cases.txt
```

The observed stderr is reproduced in `evidence/direct-merge.stderr.txt`. There
were no survivor records on stdout. The C++ source is a byte-for-byte copy of
the `machine215/research/direct_merge.cpp` member of the named incoming encoding
research archive. It was read and compiled for this finite screening task.

## Limits

Both short-transfer searches here use the append-one precursor with table hash
`d71dd41a5550584738b8aff01b990a1dc3eb93537610df270315f1132aa4b652`.
The final primary ST215 candidate uses append-zero. None of these negative
results is a lower bound on state count, an exhaustive search over 214-state
machines, or a claim about blank-tape nonhalting.
