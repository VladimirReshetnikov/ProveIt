# Runtime and bootstrap audit for the ZFC consistency machines

This folder contains two reproducible computational checks made on 2026-10-16.
It contains **no newly certified blank-tape machine below 253 working states**.
The 252-state transition system audited here is the previously reported
runtime-only quotient, whose correct blank-tape initialization is still open.

## Results

1. All **8,391 instruction/branch cases** of the published register program pass
   the upstream Python symbolic executor at each of the fixed gaps **D=36** and
   **D=37**. All 8,391 also pass with the symbolic gap **D=38+n**, for arbitrary
   natural n. Together these checks cover every D>=36 at the level of this Python
   checker and its register-box contracts. The register values themselves are
   arbitrary throughout; this is not testing a finite list of register values.
2. A literal simulation of the known 252-state runtime quotient, started in old
   state 64 on the blank tape, was extended to **1,000,000,000 moves**. It visited
   old dispatcher state 96 **103,173 times**. No visit had both a canonical legal
   program-counter encoding and a complete register-tape frame with **D>=36**.
   Nine visits had the weaker syntactic tape shape, but their PC data failed the
   legal instruction-path/padding check. The final state was old state 48, the
   head was at coordinate 9090, and the tape contained 17,551 ones, with first and
   last ones at coordinates 3 and 30000.

The second result is a **bounded negative search**, not a proof of nonhalting,
eventual failure, or the impossibility of initializing a 252-state machine. The
first result improves the immediately usable runtime precondition in this
independent audit; it does not supply a blank-tape bootstrap. No priority claim
is made for the numerical threshold D=36: related author-side conventions use
H=D+1, and previous reports already discuss small-gap bounds.

## Exact tape and gap conventions

The dispatcher uses old state 96 and reads the first PC cell. If the head has
coordinate h, the left marker is a one at h-1 and the register header is a one
at h+D. The D cells strictly between the two markers contain

`P 0^k`, where `D = |P| + k`.

Thus the marker-to-header coordinate difference is **H=D+1**. D=36 means that
the header is 36 cells to the right of the head, or 37 cells to the right of the
left marker. The right tape after the header is the concatenation of blocks
`0 1^(v+1)`, one for each register value v, followed by blank exterior. There are
at least nine blocks; further blocks represent spare storage. The physical
order of the nine source registers is:

| Physical position | Register |
|---:|---|
| 0 | wffstack |
| 1 | param1 |
| 2 | axiomcode |
| 3 | scratch2 |
| 4 | scratch1 |
| 5 | prooflist |
| 6 | nextproof |
| 7 | topwff |
| 8 | param2 |

The program is a complete binary instruction tree with 6,459 internal nodes,
6,460 leaves, and maximum leaf depth 34. A legal PC tape consists of a leaf path
followed only by zeros up to the header. A source PC ending at an internal node
has the same tape as the unique leaf reached by following its implicit trailing
zeros. The bootstrap scanner checks all 6,460 padded 34-cell words, then the
zero padding from position 34 to the header.

The upstream Coq development chooses D0=40. Its design document explains that
its affine prototype accepts 38+n but can fail to peel a run n+0 when given the
single affine family 37+n. Our two finite specializations set the coefficient of
n to zero and directly handle those boundary cases. They retain the same
unbounded register-box representation and unchanged box transitions. This is
why passing the fixed D=36/37 cases is stronger than merely repeating the D0=40
audit, while still falling short of a new Coq theorem.

## Machine definitions and attribution

All counts exclude the halting state and use a two-symbol, one-tape, two-way
infinite tape with blank symbol 0. The preserved numeric labels are labels,
not an indication that deleted states are charged.

`sources/zfc_254.tm` is the Mira-Cult 254-state table as vendored in
`jeff87654/busy-beaver`. The Python reproducer forms the **known** runtime-only
252-state table by deleting both rows of old states 5 and 8 and changing
`(3,0)` to `(write 0, move L, target 48)`. It checks that the remaining table has
252 working states, 504 rows, and no target referring to a deleted state. The
literal simulator starts in old state 64. Old state 254 is the halt target.
The public 253-state machine is included separately as a reference and is not
replaced by that exploratory start.

The runtime-only quotient's 55 protected register-box rows agree exactly with
the original 254-state table. Their checking is part of the reproducer. Box
semantics come from the upstream design and formalization. The scripts here do
not re-prove those semantics, re-run `coqchk`, or internalize the final theorem
inside ZFC. The preserved `symexec.py` is upstream code; `fixed_gap_audit.py`
extracts its function definitions without importing its command-line driver.

### Pinned references

- Jeff repository commit:
  `297ab8df7e5de329605c3875b4934643b371a5e3`.
  [254-state README](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/README.md),
  [TM design](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/design/tm.md),
  [end-to-end theorem](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/e2e/E2E254.v).
- The 253-state formalization was an open, unmerged
  [upstream PR 20](https://github.com/jeff87654/busy-beaver/pull/20) when inspected;
  its head was `mira-emmy/busy-beaver` commit
  `0d544f2a2e3c18f12278441a74b7879f31cbe856`, directory `ZF/m253`.
  The PR reports completed rebuilding and assumption/kernel checks. Those
  reports were inspected, not independently rerun here.
- The matching 253-state table was obtained from ProveIt commit
  `426592ce97e52d309bfb8f0132411556650b7ac1`, path
  `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm`.

See `PROVENANCE.json` for exact per-file URLs and SHA-256 digests. The GitHub API
reported `license: null` for both the Jeff and Mira-emmy repositories. The pinned
Jeff tree contains no root or ZF/m254 license file; licenses elsewhere concern
other vendored code. No license is inferred or newly assigned to these third-party
source snapshots. Their attribution and existing source notices are preserved.

## Reproduction

Requirements: Python 3 with its standard library and a C++17 compiler. No network
access, third-party Python package, or Coq installation is required for these
two checks. Run the following from this folder:

```sh
python3 fixed_gap_audit.py > results/fixed_gap_results.json
g++ -O3 -std=c++17 -Wall -Wextra -pedantic bootstrap_extension.cpp -o bootstrap_extension
./bootstrap_extension sources/zfc_254.tm results/pc_words_34.txt 1000000000 36 > results/bootstrap_1e9_gap36.json 2> results/bootstrap_1e9_progress.log
```

The first command validates the four source hashes before doing any symbolic
work. It creates `results/pc_words_34.txt` directly from the pinned program tree
and checks the expected node, leaf, branch, and maximum-depth counts. The second
check executes every TM move literally. Its fixed finite backing array is
bounds-checked; an out-of-range head aborts with an error rather than changing
the machine semantics. No such abort occurs in the recorded run.

The `max_executor_steps` fields in the symbolic results count prototype executor
operations, including accelerated scans and box applications. They are **not**
literal TM transition counts. By contrast, the billion-move bootstrap count is
a count of individual transition-table moves.

## What remains open

A usable new blank-tape reduction would need a concrete initialization path to
a canonical dispatcher frame, a proof that the frame reaches the intended
enumerator root, and a semantic invariant for the contents of its theorem
registers and theorem stack. Arbitrary integers in those positions cannot be
accepted merely because the physical tape is well formed. Our frame scanner
does not test theorems or prove these logical invariants; in this run it finds
no canonical D>=36 frame to which such a test could be applied.

An exploratory simulation of smaller-gap configurations encountered gap D=32
and very large pairing computations. We did not complete the additional tape
contracts needed to justify crossing its first unsupported control case.
Those exploratory traces are deliberately excluded from the validated subset.
