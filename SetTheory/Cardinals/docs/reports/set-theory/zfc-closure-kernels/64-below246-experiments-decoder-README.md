# Decoder and detector experiments on Context246

These experiments found **no machine with fewer than 246 states**. They do
produce a different 246-state detector implementation, exact reproducible
search records, and a sharper local synthesis problem. No unsuccessful search
here is a lower bound on the possible state count of a ZFC machine.

## Inputs and layout

The commands below run from the archive root, with this directory at
`experiments/decoder` and the unmodified Context246 archive at
`baseline/context246`:

```sh
export ZFC246_BASE="$PWD/baseline/context246"
```

All baseline-dependent scripts honor `ZFC246_BASE`. `fold_search246.py` and
`check_detector_bootstrap.py` additionally honor `ZFC246_TABLE` for an
experimental transition table. No input file is modified. Standard Python 3
is sufficient except for synthesis, which requires the version in
`experiments/counter/requirements.txt`. A locally installed solver directory can alternatively be
specified through `ZFC246_VENDOR`.

The exact baseline is `machine/zfc_prefix246_old.tm`, SHA-256
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.
It has 246 working states, start 95, dispatcher 96, and halt 254. The optional
source ancestry diagnostic uses the bundled `Dag254.v`, SHA-256
`538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3`, from
<https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/coq/prog/Dag254.v>.

## Fresh uniform and mixed folds

```sh
python experiments/decoder/fold_search246.py --family both --seconds 600
```

The driver first verifies all 8,391 guarded source cases against Context246's
affine instruction oracle. It protects the 42 literal state/read rows in the
four block, three register macro, and nine marking induction traces, together
with their destination labels. The dispatcher is fixed. There are 222 eligible
deleted states. The driver asserts the theorem names, counts, support-row
count, and literal equality of those rows to the original machine.

A uniform recipe deletes one state and redirects its incoming references to
a retained state. A mixed recipe also copies one of the deleted state's rows
onto the retained state, subject to the support constraints. Symmetric and
duplicate mixed recipes are omitted. Each candidate is checked on every
baseline-affected case, shortest first; a survivor would be checked again on
all 8,391 cases before any bootstrap search.

| Table | Family | Recipes | Affine checks | Survivors |
|---|---|---:|---:|---:|
| Exact Context246 | Uniform | 54,390 | 129,741 | 0 |
| Exact Context246 | Mixed | 49,688 | 717,456 | 0 |
| Alternate detector8 | Uniform | 54,390 | 122,933 | 0 |
| Alternate detector8 | Mixed | 49,704 | 624,388 | 0 |

The complete original and alternate searches took 257.93 and 224.94 seconds,
respectively. Every recipe failed within the recorded 1,000-rule fuel and the
oracle's supported affine operations. `unsupported`, `fuel`, and `missing` are
checker rejection categories; none means a proof that the corresponding
machine cannot be correct under a different invariant.

Records: `both-fold-search246.json`, `detector8-fold-search246.json`.

## Why the existing counter cannot simply be shortened

```sh
python experiments/decoder/chain_probe.py
python experiments/decoder/map_chain_semantics.py
python experiments/decoder/long_entry_probe.py
python experiments/decoder/state2_probe.py
```

The source PC paths have at most seven consecutive zeros, but legal execution
creates an eight-zero transient at 18 decrement sites. The one-suite literal
census reaches state 74 reading 1 in both guards of each site: 36 guarded cases
out of 8,391. Thus removing the last zero-counting state using only the source
path bound is unsound. These sites all lie under prefix `11101001001` in the
axiom generator: ten decrement register T, seven W, and one L.

`map_chain_semantics.py` aligns the *in-order leaf sequences* of the original
DAG and the reassociated decoder tree. All 6,460 operation kinds and all 1,931
decrement register arguments agree. This gives the affected decrement sites'
original helper ancestry. Directly following a reassociated PC in the
original DAG is invalid. The map is a provenance diagnostic, not a complete
equivalence proof: 678 increment operands differ because some commuting
increment pairs have exchanged order, and control addresses also differ.

The separate state-2 census identifies `20/0` as the caller that enters an
unbounded zero scan. Its observed runs range from 37 to 72 zeros in the chosen
finite suite. Other observed incoming contexts are bounded (20/1 at most six,
42/1 zero, and 143/1 at most one). A direct `2 -> 4` fold therefore loses the
long scan needed at `20/0`; the runtime experiments separately tried all 980
single-row replacements of that caller without a survivor.

The long-exit census records 21,316 visits to original `74/0`; every one has a
blank left exterior in this finite suite. This census is **not** the proof of
that invariant. The separate universal affine entry audit supplied by the
theory audit checks all 8,391 arbitrary-parameter instruction contracts and
proves the additional zero at coordinate -8 needed below.

## The local synthesis contract

The eight-state suffix is labelled `[6,9,13,19,29,41,58,74]`. Its only external
incoming row is `4/0 = 0 L 6`. At entry to state 6, put the head at coordinate
0. The just-read cell +1 is zero; cell +2 is one. The latter follows because
every incoming baseline row to state 4 is `1 L 4`.

There are eight short cases. For `k=0,...,7`, the first left one is at `-k`
and the cells from `-k+1` through +1 are zero. The required output is the exact
original tape, state 4, and head `-k-1`. Unknown tape outside `[-k,2]` may not be
read. The long case has zeros in a recorded window to the left. Solver states
0 through n-1 are free internal states; target n denotes 4, and n+1 denotes 84.

There are three explicitly different search scopes:

1. The initial fixed-row and relaxed-row runs allowed a larger known blank
   window down to -16 and a long exit at an arbitrary zero at or left of +1.
   Their results are all timeout/unknown. They do not establish a universal
   replacement for arbitrary left exterior at coordinate -8.
2. The finite-window runs allow long active reads only in `[-7,2]` and require
   an exit to 84 at a zero in `[-7,1]`. Such a successful model would implement
   the intended scan back to the known one at +2. Its equivalence to the old
   suffix uses the actual source-entry guard that cell -8 is zero.
3. The exact-exit runs also restrict long active reads to `[-7,2]` but require
   the exit to be exactly state 84, head -8. This matches the original suffix
   *before* state 84 reads any opaque exterior and therefore avoids that
   extra guard in a local replacement proof.

The exact old row is `74/0 = 0 L 84`. Its movement matters. If the first left
one were at -8, the old suffix would enter 84 on that one. A replacement that
instead enters 84 at -6 would continue to the right-hand one at +2. These are
different on that excluded context; do not silently identify the contracts.

## Solver commands and interpretation

The root counter directory retains the initial fixed-entry-row solver and its
records, including the 8-state positive control. The relaxed driver in that directory leaves
the entry's read-1 row free by default, because it may be useful later in a
tape-restoring computation. `--fix-one` restores the original restriction.

```sh
python experiments/counter/synthesize_detector.py --states 7 --steps 16 --seconds 180
python experiments/counter/synthesize_detector.py --states 7 --steps 20 --seconds 180
python experiments/counter/synthesize_detector.py --states 7 --steps 24 --seconds 180
python experiments/counter/synthesize_detector.py --states 7 --steps 16 --seconds 180 --long-min-read -7 --long-min-exit -8 --long-exit-head -8
```

To reproduce the earlier larger-window relaxed scope, pass
`--long-min-read -16 --long-min-exit -16`. To reproduce the exact 8-step boundary
controls, pass `--steps 8 --long-min-read -7 --long-min-exit -8 --long-exit-head -8`,
with `--states 7` or `--states 8`. `--output` sets an exact result filename.
The result JSON records the state count, step bound, footprint, exit
restriction, optional fixed rows, renaming restrictions, solver version,
timeout, and answer. All `unknown` records include the timeout reason. A
bounded UNSAT result would concern only the recorded family and is not a
general state lower bound.

The completed run ledger has nine timeout/unknown outcomes for 7-state
searches, one bounded 7-state UNSAT control, and two 8-state SAT controls. In
the exact-exit 8-step family, 7 states was UNSAT in 0.86 seconds and 8 states
was SAT in 0.35 seconds. The 7-state control has a simple explanation: to go
from head 0 to head -8 in at most eight steps, every move must be left. Exact
tape restoration forces each visited zero to remain zero. A repeated internal
state would then repeat the same zero transition forever, so eight distinct
internal states are necessary for this particular eight-step contract. This
argument says nothing about a detector allowed additional steps.

`run-ledger.json` records every run, its exact family, command, result hash,
and outcome. Three exact-exit records retain their original prose scope plus
an explicit metadata correction: their solver constraints always required
head -8, without assuming the symbol at that uninspected exit cell is zero.

## Alternate 246-state machine

The initial 8-state/8-step SAT model is in
`experiments/counter/result_n8_t8_wNone.json`, SHA-256
`ce4ac75cc5fcc0f1f6235b36f1fba7d7e2ee893272da61c02a5ece41c3f81159`.
It writes no tape cells and sometimes bounces right on the detected one before
returning left. Independent literal replay gives short-case durations
`[1,2,7,8,7,8,7,8]` and long-case duration 8. Its active reads stay within
`[-7,0]`; the long exit is head -6. Exact traces are in
`detector-replay-result_n8_t8_wNone.json`.

```sh
python experiments/decoder/verify_detector.py experiments/counter/result_n8_t8_wNone.json
python experiments/decoder/install_detector.py experiments/counter/result_n8_t8_wNone.json --output experiments/decoder/detector8-context246.tm
python experiments/decoder/audit_detector_support.py
ZFC246_TABLE="$PWD/experiments/decoder/detector8-context246.tm" python experiments/decoder/fold_search246.py --family both --seconds 900 --output experiments/decoder/detector8-fold-search246.json
ZFC246_TABLE="$PWD/experiments/decoder/detector8-context246.tm" python experiments/decoder/check_detector_bootstrap.py
```

The installed table SHA-256 is
`2e4c60cf14947c9ebb8e4bf999f9cd0ac995d09d16bb8b84e5c2fba922f79b1b`.
All 42 register-induction support rows remain literal matches and all 8,391
affine instruction contracts pass directly on the new table. A fresh blank
run reaches a complete safe root after 409,449 steps: dispatcher 96, head -5,
header 176, empty PC, logical register values
`[N,T,W,A,D,H,X,Y,L]=[3,0,0,0,3,0,0,0,0]`, and 167 spare blocks of value 1.
This finite prefix and the inherited safe-root result complete the same proof
interface as the baseline. No new kernel-checked endpoint theorem is claimed.
The table still contains 246 working states.

## Curated files

Include the scripts named above, their JSON/TM outputs, `requirements.txt`,
and `Dag254.v`. The exploratory `map_chain_sites.py` and `chain-site-map.json`
used an invalid direct-PC ancestry method and are deliberately excluded from
the curated deliverable; `map_chain_semantics.py` replaces them. Exclude Python
bytecode caches and local solver binaries.
