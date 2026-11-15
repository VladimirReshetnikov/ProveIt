# Bounded physical reduction searches

This directory records additional reduction work on the pinned PA194 corpus.
No sub-194 machine was obtained. These are negative results in explicitly
bounded transformation classes, not a lower bound on the number of states
needed for a PA consistency machine.

## Inputs and status

The upstream pin is `8d31445d858761a8f6150c2e5012adae8895e932`.
`inputs/primary.native.tm` is the primary PA194 table in its native labels,
with start 74 and halt 254. Its SHA-256 is
`e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54`.

`inputs/corpus/` contains 530 distinct complete literal tables, each with 194
working states and 388 rows. They comprise 118 distinct native-label tables
found in the six current incoming archives, and additional syntactically
eligible combinations of the loop-continuation, selector, and accelerated
return patches. Their filenames are their SHA-256 hashes. The provenance
ledger is `receipts/corpus_meta.json`.

The 530 inputs are a search corpus. No blanket correctness or novelty claim
is made for the added combinations; they were not all individually calibrated
or certified. In particular, a disjoint set of edited rows is insufficient
by itself to prove that semantic transformations compose. The separately
delivered machine constructions have their own exact certificates.

## Reachable-window invariant

For radius K, an abstract configuration consists of a control and the
2K+1 tape bits at offsets -K through K from the head. Start with the blank
window in control 74. Execute the literal current transition, shift the
window, and allow both possibilities for the newly entering boundary bit.
The least closed set of these abstract configurations contains every actual
blank-start window. This follows by induction on the number of literal
machine steps, without any hypothesis about arithmetic consistency.

This finite abstraction may admit windows that the actual machine never
visits. Rejection on one of those windows can therefore lose a valid
optimization. It cannot justify calling an unsuccessful search a global
lower bound.

## Search classes

1. `local_search.cpp`: For every control/read-bit pair, enumerate every
   possible first action and check whether it realizes the original single
   transition by a bounded path through unchanged rows. Full tape equality,
   head position, and exit control must match. A path may not leave the
   window. Intersect these candidate actions for every pair of controls;
   intermediate executions of either control being merged are forbidden.
   Incoming targets are redirected through the proposed state identification.

2. `edge_bypass.cpp`: Try to remove a non-start, non-self-looping control by
   changing every row that enters it. Each changed incoming row must simulate
   the original incoming transition followed by the removed control's next
   transition. Paths avoid the removed control and every changed incoming
   row until they rejoin the old run. This allows changing the incoming write
   and direction, beyond ordinary state identification.

3. `multisync.cpp`: Generalize the first search by permitting rejoining at
   any of the next 16 original configurations, instead of the immediate next
   configuration. The original and replacement paths remain bounded and
   have identical complete tape and head at the matched endpoint.

4. `recursive_folds.cpp`: Allow both replacement rows of a merged control
   to be arbitrary, and allow the replacement execution to revisit that
   merged control. For each control pair, a sound first-reentry prefilter
   screens the 776 possible actions on each bit: four write/direction choices
   times 194 targets (the 193 retained working controls plus halt). The
   eliminated control is excluded as a redundant target because it redirects
   to the kept control; halt is included. Every surviving pair of
   actions is tested against every reachable window of both original
   controls. The target is the original single-step result with the two
   controls identified. For a 194-state table this represents 18,721 control
   pairs and 11,273,336,896 possible two-row definitions before filtering.
   The prefilter only rejects a first action when the unmodified portion of
   its path cannot reach either the target configuration or a first reentry
   into the merged control within the allowed window and step budget.

5. `selfloop.cpp`: A direct exhaustive subsearch of the preceding class,
   restricted to replacements with at least one immediate self-loop row.
   This served as an additional independent enumeration of those cases.

The local checks preserve the entire tape because every inspected or changed
cell lies in the window, and no exterior cell is changed on either trace.
If a positive certificate were produced, the finite tables of local traces
would support a primitive-recursive bounded stuttering proof. No positive
193-state certificate was produced in this work.

## Completed runs

| Search | Inputs | Radius | New-step bound | Result |
|---|---:|---:|---:|---|
| Nonrecursive local folds | 530 | 5 | 64 | No merge |
| Edge bypass | 530 | 5 | 64 | No elimination |
| Common-future folds, at most 16 old steps | 530 | 5 | 64 | No merge |
| Nonrecursive local folds | Primary | 9 | 128 | No merge |
| One neutral row rewrite, then local folds | 348 rewrites of primary | 5 | 64 | No merge |
| Recursive folds | Primary | 7 | 64 | No merge |
| Recursive folds | PA194AX11H_SF | 7 | 64 | No merge |
| Recursive folds | PA194LC_AX11H_SF | 7 | 64 | No merge |

The primary radius-9 abstraction has 10,590,743 abstract configurations.
The primary radius-7 abstraction has 898,177 configurations. The recursive
search fully tested 1,227,299 surviving two-row definitions on the primary,
1,167,897 on PA194AX11H_SF, and 1,150,094 on PA194LC_AX11H_SF. All prefiltered
definitions and all fully tested definitions failed in those bounded classes.

The 348 neutral row rewrites were first certified against the original
radius-7 invariant, with up to 128 replacement steps and no intermediate
execution of the changed control. The window invariant was recomputed for
each modified table before its subsequent merge search.

## Closed-macro search candidates

Twelve source-CFG-preserving closed-macro candidates supplied by the parallel
source search were also folded to 194 controls. The supplied folds passed
28 local cases each (32 for the eight-fold node61 candidate). Recursive
folding and common-future edge bypass on each, at radius 5 and 64 new steps,
found no further reduction. The latter permits 2 through 16 old steps before
rejoining. Their physical source correctness was not asserted, and they were
not promoted as new machines. Frozen inputs are in `inputs/closed/`; results
are in `receipts/closed_scan.json`.

## Reproduction

The C++ files require a C++17 compiler and no external libraries. Each reads
literal rows of the form `state read write L-or-R target`; native start and
halt labels are 74 and 254. For example:

```
g++ -O1 -std=c++17 code/recursive_folds.cpp -o /tmp/recursive_folds
/tmp/recursive_folds inputs/primary.native.tm 7 64
```

The program writes found reductions to stdout. Empty stdout is the negative
result, and stderr records context and candidate counts. `reproduce.py`
compiles the searchers into a fresh temporary directory, validates the frozen
input hashes and table shapes, and repeats a compact or full suite. It saves
fresh receipts under a requested output directory.

```
python3 reproduce.py --output replay
python3 reproduce.py --all --output replay_all
```

`--all` repeats the three 530-table searches and the 348 neutral-rewrite
searches. It takes longer. The stored receipts report the completed original
runs. Neither the C++ searches nor the Python launcher is a proof-assistant
kernel, and none establishes an absolute iPRA/Con(PA) calibration.
