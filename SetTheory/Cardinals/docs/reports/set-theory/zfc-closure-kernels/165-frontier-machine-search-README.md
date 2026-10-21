# Machine-level research packet

This packet contains two new **215-state** intermediates with complete
quantified runtime receipts, and reproducible searches for a state saving.
It does **not** establish a 214-state Con(ZFC) machine. The 214-state scanner
under rejected/ has a concrete primitive-contract counterexample.

The baseline is ProveIt commit
2762b8a183830b1f5a30cf059ffb4d92e77cddde, candidate-k215.
The default sibling baseline location is ../baseline/k215; every Python
script accepts --baseline PATH when the archive uses another location.

## New intermediates

| File | Working states | Changes from the preceding table | Quantified cases |
|---|---:|---|---:|
| accepted/original215.native.tm | 215 | Pinned K215 baseline | Baseline packet |
| accepted/cb1_215.native.tm | 215 | Change row (8,1) from 1 R 13 to 1 R 103 | 6,177/6,177 |
| accepted/normalized215.native.tm | 215 | Change (13,0) to 0 R 49 and (13,1) to 0 R 60 | 6,177/6,177 |

Both new tables use accepted/cb1_sites.json, with 4,752 leaf occurrences,
202 distinct source DAG nodes and maximum address depth 47.

The source change appends CB1 to the initial restoration loop H:
((G,(F,(CI0,H))),B) becomes ((G,(F,(CI0,(H,CB1)))),B).
The appended pair is already represented by native state 103. It changes
enumeration timing and candidate numbering; its calibration requires the
separate scheduler proof in the companion theory report. Source runtime
verification alone does not prove that calibration.

The q13 normalization has an exact local stuttering proof in
construction/normalization-proof.txt. It preserves the CB1 table's
halting behavior on the blank tape. The complete blank startup traces
reach the same calibrated seed in 88,116 and 87,920 steps respectively.

Run reconstruction:

~~~sh
python3 reconstruct.py
~~~

The small runtime summary JSON files are readable directly. Full symbolic
case receipts and full startup traces are compressed as .json.gz.
The checker proves induction-based contracts for all natural primary
register values, every natural gap and every nonempty finite spare list,
with zero exterior. It is self-authored Python, not a proof-assistant kernel.

To regenerate a quantified runtime receipt from a new table:

~~~sh
python3 ../baseline/k215/code/runtime-inputs/validate_native.py accepted/normalized215.native.tm accepted/cb1_sites.json regenerated-normalized
~~~

## Concrete scanner counterexample

Deleting native scanner state 50 and retargeting (34,0) to 0 L 75 yields
214 working states. It passes 6,104 of 6,176 quantified cases, but fails
72 cases at 37 source leaves. The stored rejected receipt retains every
successful symbolic case as well as all reported failures.

The portable replay uses site 26, CD1 at address 1101001001000000,
all primary registers zero, one zero spare, and gap zero. The baseline
returns the required frame. The shortened scanner returns a clean frame
with a program-counter one at position 12 instead of position 14.
This is an exact finite runtime-contract failure, not a claim about the
blank run's eventual behavior or a proof of inconsistency.

~~~sh
python3 replay_scanner_counterexample.py
~~~

## Finite search evidence

search/summary.json gives exact space sizes, positive-control totals,
acceptance counts and bounds. Search files reject candidates using 6,176
or 6,177 concrete primitive frames. A negative result can reflect a
runtime bound or finite tape window, so these searches do not prove an
unrestricted impossibility theorem.

The programs first run the unmodified table on every case. They record
the states or edges used by those traces, screen each alteration on a
small sample of affected cases, then check every affected case for
sample survivors. Unaffected cases follow the same trace until any
first changed transition and therefore need not be replayed.

All C++ programs accept a native table path and a concrete-case TSV path.
Composition programs additionally accept an edge-alternative TSV. The
full composition search deliberately omits large combination spaces for
states 2 and 302, and never deletes start 0 or dispatcher 84.

~~~sh
python3 generate_cases.py accepted/original_sites.json original_cases.tsv
python3 generate_cases.py accepted/cb1_sites.json cb1_cases.tsv
g++ -O3 -std=c++17 search/code/direct_merge.cpp -o direct_merge
./direct_merge accepted/original215.native.tm original_cases.tsv
g++ -O3 -std=c++17 search/code/mixed_merge.cpp -o mixed_merge
./mixed_merge accepted/original215.native.tm original_cases.tsv
g++ -O3 -std=c++17 search/code/edge_composition_full.cpp -o edge_composition_full
./edge_composition_full accepted/original215.native.tm original_cases.tsv search/data/edge_all.tsv
g++ -O3 -std=c++17 search/code/common_merge_anyrow.cpp -o common_merge_anyrow
./common_merge_anyrow accepted/normalized215.native.tm cb1_cases.tsv
g++ -O3 -std=c++17 search/code/tagged13_82.cpp -o tagged13_82
./tagged13_82 accepted/normalized215.native.tm cb1_cases.tsv
~~~

The relaxed search variants preserve the logical program counter and
nine primary register values but allow a different well-formed spare
tail, gap and frame translation. Their logs also record no accepted
state-eliminating candidate.

An early unprotected decoder-rotation experiment was invalidated by
helper-row interference. None of its tables or claims is included here.
