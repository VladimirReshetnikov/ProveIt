# Engineering result and current machine ledger

Research cutoff: ProveIt `af518abcf8ca2a7c1b795c07973885041aee0d25`,
including the reports arriving at that commit. Prepared 16 October 2026.

## New measured component: a compact, exact blank initializer

The new code in `compact_initializer.py` replaces the clean Mira assembler's
literal initializer, without changing a runtime transition. On the recovered
219-node source DAG, the complete binary machine drops from **408 to 341
working states** for zero registers, and from **410 to 343** with
`nextproof=2`. This is an improvement to the *editable control assembler*.
It is not competitive with the attributed optimized 253-state machine, and
it is not a new calibrated ZFC-consistency-machine bound.

The earlier clean assembler used one state per written or crossed tape
cell. Its zero-register initializer paid 122 states: 18 register cells,
one header, 102 gap zeros, one left marker. The new construction pays 55
states, emits a 104-cell gap and the same nine-register frame, and takes
880 transitions from a blank tape. It trades irrelevant finite startup time
for a smaller complete description.

| Quantity | Prior clean control | New component integration |
|---|---:|---:|
| Source register DAG nodes | 219 | 219 |
| Runtime working states | 286 | 286 |
| Zero-register initialization states | 122 | 55 |
| Gap zeros | 102 | 104 |
| Complete working states | 408 | 341 |
| Complete binary rows | 816 | 682 |
| Blank initialization transitions | 122 | 880 |
| Zero-register output one-cells | 11 | 11 |

The runtime's 572 rows are re-extracted by symbolic labels before and after
the replacement, and are identical. Numeric state labels are reassigned.
The existing per-instruction affine checker passes all 8,391 cases for
each new machine, including both outcomes of all 1,931 decrement sites.
Those checks still assume the four published register-box contracts and
have no kernel-checked soundness theorem. The initializer itself has the
direct elementary proof below and a separate literal full-tape replay.

## Exact initializer theorem

Fix positive integers n,m and nine nonnegative initial register values
whose sum is S. The physical register order is the existing assembler's
`(2,4,3,7,6,8,0,1,5)`. Each register of value v occupies `0 1^(v+1)`.
The new deterministic, binary, single-tape initializer has

    G = n(m+2)+2
    N_init = S+28+2n+m
    T_init = S+28+6n+(m+2)n(n+2).

It starts on an all-zero tape at head position 0. After exactly T_init
transitions it enters its external runtime target. At that moment its tape
is exactly a marker 1, G zeros, a header 1, and the nine register blocks;
the head is immediately to the right of the marker. All other cells are
zero. No scratch marks or surplus register blocks remain. Both binary
transitions of every working state are supplied; there is no implicit
halting row.

### Construction and proof

Write the register blocks right to left, then a header 1, an auxiliary 1,
n copies of `01`, a separating 0 and a frontier 1, continuing leftward.
Use coordinates relative to the header. The auxiliary delimiter is at -1,
the n counter markers are at -3,-5,...,-(2n+1), and the frontier is at
`f_0=-(2n+3)`. The head then turns right. The setup uses
`S+22+2n` states and the same number of transitions.

The main loop scans right to the first 1 and tests its right neighbor.
An isolated 1 is the next counter marker. Erase that counter, scan left
through zeros to the frontier, erase the frontier, move m places left and
write its replacement. Restart the rightward scan. The only adjacent
`11` encountered by the test is the auxiliary delimiter and the header.
When that pair is found, erase the auxiliary 1, scan left to the remaining
frontier, preserve it, and move right into the runtime entry state.

The induction invariant after j completed iterations, for 0<=j<=n, is:

* the frontier is at `f_j=-(2n+3)-jm`;
* precisely the first j counter markers in left-to-right order have vanished;
* the remaining counter markers, auxiliary delimiter, header and registers
  have their original values;
* the head is at `f_j+1`, in the rightward scan state;
* every cell between the frontier and the next remaining counter is zero;
* there are no other nonzero cells besides those just listed.

For j<n the next counter is at `c_j=-(2n+1)+2j`, so its distance from the
frontier is `d_j=2+j(m+2)`. It is isolated, hence the counter branch is
taken. Erasing it and shifting the unique frontier preserves the invariant
with j replaced by j+1. The scan never crosses the header or touches a
register. After n iterations, the frontier is at
`-n(m+2)-3=-(G+1)`, and the delimiter branch erases the only auxiliary mark.
The desired output follows, including the absence of garbage anywhere on
the tape.

There are four loop-control states (scan right, test, consume, scan left),
m stride states, and two final cleanup states. Adding setup states proves
the N_init formula. Iteration j takes `2d_j+m+2` transitions. Summing gives
`(m+2)n^2+4n`. Final cleanup takes `2G+2` transitions, which with setup gives
the T_init formula. This is a direct induction proof for all n,m and all
register vectors, not an inference from a finite test run.

The register-specific constant 28 generalizes to `2r+10` for r unary
register blocks. The binary construction needs no separate tape alphabet,
prepared input, or implicit initial data.

### Choosing the parameters

To meet a required gap g, minimize `2n+m` subject to positive integers n,m
and `n(m+2)+2>=g`. For fixed n the best m is

    max(1, ceil((g-2)/n)-2).

Thus parameter selection is an exact small integer minimization, not a
heuristic machine search. For g=102 its minimum is 27. Choosing n=6,m=15
gives G=104 and minimizes runtime among the minimizers in the implemented
tie rule. The initializer therefore has 55+S states and 880+S steps.

For large g choose n near sqrt((g-2)/2), and then m by the displayed
formula. This gives `N_init=S+O(sqrt(g))`, compared with the clean
assembler's direct `S+g+20`. This is an upper bound for this explicit
construction. No global novelty, optimality or lower-bound claim is made.

## Reproduction and delivered evidence

Run, from the engineering directory:

    python -B compact_initializer.py --output /tmp/zfc-compact-initializer

All needed dependencies are included as unmodified, attributed source
files. Python's standard library is sufficient. The output directory must
be outside `vendor/ProveIt`. The program performs:

* 864 literal initializer runs: n=1..12, m=1..24, three register vectors;
* 300 independently enumerated checks of the parameter minimizer;
* both complete source-DAG compilations with the new initializer;
* byte-for-byte runtime-row comparison under symbolic relabeling;
* 8,391 per-instruction affine cases for each integrated table;
* exact replay of each complete numeric table to its runtime entry;
* independent reparsing of every emitted row.

The supplied result files are the outputs of that execution. The symbolic
runtime checks carry the upstream assembler's explicit limitations. The
finite checks are neither consistency evidence nor a complete compiler
simulation proof.

| Table | States | SHA-256 |
|---|---:|---|
| `dag219-compact-zero.tm` | 341 | `79189306aba6a735f38acd4eb3b9643f18a944b907cdb69204659b95ee99c1d8` |
| `dag219-compact-nextproof2.tm` | 343 | `e98ae77b4124417e7e59212a2cbca1d0ecb0a87a17ed86706d0d195e0dc32a4f` |

## Prior-work ledger at the cutoff

The relevant counts measure different mathematical and computational objects.
The following distinctions must survive any report synthesis.

| Artifact | Measured status | Endpoint limitation |
|---|---|---|
| Attributed upstream original | 254 working states | Published Coq finite-refutation equivalence; internal ZFC/PA arithmetization requires a separate bridge. |
| Attributed upstream mira-emmy reduction | 253 working states | Existing reduction of Mira-Cult/Jeff work, not a new result here. The altered boot takes 312,975 steps and reaches logical registers `[5,0,0,0,2,0,0,0,0]`. |
| Batch144 source04 core | 252 runtime states | Deleting the253 initializer does not initialize the core. All blank starts are uncalibrated. |
| Batch144 source09 core | 252 prepared-tape states | No blank initializer; complete blank-start variants have267/256 states. |
| Frozen project candidate | 252 states,504 rows | Changed base3/equality-free calculus and compiler remain uncalibrated. |
| Latest PSC-only component | 252 named states,503 rows | Explicit dead-quantifier counterinterpretation proves reduced calculus incomplete. Distinct from the frozen C/G candidate. |
| Incoming grammar report | Original-rho6 250 / dual249 complete states | Exact138-macro grammar preservation; incomplete theory/compiler endpoint. |
| Incoming parameter-permutation/grammar report | Original-rho6 248 / dual248 complete states | Each has3,394 operation-pair certificate; retained current calculus still requires full calibration. |
| New compact clean assembler | 341 /343 complete states | Exact initializer with unchanged runtime; full runtime/compiler and ZFC endpoint still separate. |

The source08 219->207 Wade DAG reduction (281->269 machine) and source09
203->202 decoder reduction (267->256 after folds) are already prior work.
This experiment does not claim or repeat those reductions as new. Likewise,
exact macro-word Re-Pair is prior work, including the incoming248 tables.

Current source primary URLs:

* https://github.com/VladimirReshetnikov/ProveIt/commit/6d8bc7f1ba02c83e54757366f019f61b966ed0b7
* https://github.com/VladimirReshetnikov/ProveIt/commit/e7c4cadf9b180e4b1801755b09777a7572412360
* https://github.com/VladimirReshetnikov/ProveIt/commit/af518abcf8ca2a7c1b795c07973885041aee0d25
* https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/Computability/BusyBeaver/Research/ZFC/mira_backend.py
* https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/Computability/BusyBeaver/Research/ZFC/mira_backend.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/Computability/BusyBeaver/Research/ZFC/psc_backend_experiment.md
* https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/prog/Dag254.v
* https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/machine/zfc_254.tm
* https://github.com/jeff87654/busy-beaver/pull/20

Incoming archive provenance and stronger logical countermodels are audited
by the other research strands; this engineering note does not override them.
