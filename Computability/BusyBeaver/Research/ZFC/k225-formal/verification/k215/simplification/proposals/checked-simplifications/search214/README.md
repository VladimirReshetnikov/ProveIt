# Coordinated marker sharing toward 214 states

This supplement records a new bounded synthesis family and its negative result.
**It contains no accepted 214-state ZFC machine.** The eighteen input machines are
215-state reference machines, not new discoveries in this supplement. The
synthetic positive control is only an 11-to-10-state local gadget.

## Construction being tested

Suppose `(p,q)` and `(u,v)` are disjoint pairs of old controls. In each pair one
read branch is shared, and a bit next to the head distinguishes the two old
origins on the other branch. The two pairs use the same marker side. Merge
`q` into `p` and `v` into `u`, and add one fresh selector `H`.

At the changed branch of `p`, write tag 0 (or 1), move to the adjacent marker,
and enter `H`. At the changed branch of `u`, write the opposite tag, move to
that marker, and enter `H`. The selector preserves the marker and returns to
the tagged cell, entering provider `f0` or `f1` according to the marker. The
existing provider paths must restore the original tape effect and meet a
positive old execution with the mapped control and exactly the same head and
whole tape.

This reduces the count by one if it succeeds: `215 - 2 + 1 = 214`.

The temporary tag is the distinction from the earlier double-marker search.
Both source pairs may have their conflict on read 0, or both on read 1; the old
scanned bit need not itself identify the pair. Moreover, the C++ search runs
all four new rows together and allows provider paths to revisit the retained
merged controls and selector. The earlier strict-provider filter excluded
those revisits. The construction still has a restricted shape: it does not
synthesize arbitrary 214-state transition tables.

## Correctness obligation for a successful construction

Let `pi` identify the two deleted labels with their retained labels and fix all
other controls, including halt. The old machine has a finite-window invariant
`I` containing the blank initial configuration and closed under every old step
and both possible entering exterior bits. For each invariant window at an
affected old branch, require a positive old path and a positive new path that
end with control related by `pi`, identical head position, and identical tape.
No path may inspect a cell outside the window. The unchanged branches simulate
in one step. These obligations suffice for blank-start halting equivalence:
iterate the positive joined blocks along the deterministic old run. A finite
old halting run reaches halt after finitely many blocks because each consumes
at least one old step. An infinite old run gives arbitrarily long new prefixes
because each new block is also positive; no block can pass through halt. The
same synchronized blocks therefore exclude a finite new halt in the divergent
old case. Finite-window equality extends to the whole tape since the exterior
is untouched.

The invariant is sound by induction on the number of old steps. Its checker
verifies the initial all-zero window and each abstract successor. Entering bits
are universally quantified by the two checked alternatives. Abstract windows
need not be concretely reachable. Consequently, rejection at one such window,
a window escape, or a 64-step limit is only a failed certificate search; none
is by itself a concrete counterexample or a lower bound.

## Actual results

All eighteen reference inputs are hash-bound in `inputs.json`. The repository pin
is `53269bcab1efc0f82d3022645bd7cf0c22d84959`. FM215 is from the separate incoming
archive at that pin, rather than an already integrated formal endpoint.

| Seed | Invariant windows | Marker pairs | Pair/tag families | Complete provider assignments | Accepted folds |
|---|---:|---:|---:|---:|---:|
| Primary K215 | 87,475 | 31 | 500 | 22,684,500 | 0 |
| GC-ZC215 | 87,963 | 35 | 690 | 31,304,610 | 0 |
| Context returns | 87,803 | 36 | 734 | 33,300,846 | 0 |
| Shallow context returns | 87,659 | 37 | 788 | 35,750,772 | 0 |
| Incoming FM215 | 87,731 | 30 | 456 | 20,688,264 | 0 |
| **Total** | | | **3,168** | **143,728,992** | **0** |

The following thirteen further frozen layouts were then searched with the same
final algorithm and bounds. Their tables come from the incoming
`ZFC215_Proof_Simplification_2026-10-21.zip` packet at the same repository pin.
The original five-seed runs above remain independently recorded.

| Additional seed | Invariant windows | Marker pairs | Pair/tag families | Complete provider assignments | Accepted folds |
|---|---:|---:|---:|---:|---:|
| 00_commands120 | 87,835 | 33 | 592 | 26,858,448 | 0 |
| 01_composed | 87,475 | 31 | 500 | 22,684,500 | 0 |
| 02_composed | 87,475 | 31 | 500 | 22,684,500 | 0 |
| 03_conditional-marker | 87,859 | 30 | 458 | 20,779,002 | 0 |
| 04_direct-transfer | 87,935 | 31 | 500 | 22,684,500 | 0 |
| 05_mp-first-transfer | 88,033 | 32 | 546 | 24,771,474 | 0 |
| 06_rebalanced | 88,083 | 30 | 456 | 20,688,264 | 0 |
| 07_reencoded | 86,323 | 32 | 540 | 24,499,260 | 0 |
| 08_rho6 | 87,835 | 35 | 688 | 31,213,872 | 0 |
| 09_rho6 | 87,619 | 34 | 638 | 28,945,422 | 0 |
| 10_zero-spare | 87,411 | 31 | 500 | 22,684,500 | 0 |
| 11_zero-spare-mp-first | 87,969 | 32 | 546 | 24,771,474 | 0 |
| m124 | 87,635 | 30 | 456 | 20,688,264 | 0 |

**Combined total: 10,088 families, 457,682,472 complete provider assignments,
zero successful folds across eighteen exact tables.** Counts are per table; no
claim is made that every pair of input tables has a nonisomorphic transition
graph or that every tested specification defines a distinct quotient graph.

Radius 5 means eleven cells. Both old and new traces are capped at 64 literal
steps. Provider targets range over the 213 retained old working controls;
halt and the new helper are excluded as direct provider targets. Old and new
paths can nevertheless reach halt or revisit the helper through the trial's
rows. Both tag orientations are tested. The two originals in a pair have a
literally equal unmodified branch. Start is excluded from the four folded
origins. Each `families` count multiplied by `213^2` gives the assignment count.
A trial is rejected as soon as a context fails; every reported trial is still
a complete pair of provider assignments, not a count of individual row tests.
These are specifications, not a claim of pairwise distinct transition graphs.
The `first` log field counts trials passing the first context only and has no
correctness significance.

The eighteen input domains have **no absent state/read-symbol row**, even when
seeded with the actual blank window. The independent checker validates all
eighteen domains with a list-of-cells successor calculation, separately from the
inherited bit-mask worklist generator.

## Positive and negative controls

`positive-control.txt` describes a synthetic eleven-control table with two
pairs that both differ on read zero. The temporary tag enables one shared
selector to reduce its local gadget to ten controls. The C++ search finds the
intended row assignment. A separately implemented dictionary-tape simulator
checks every one of 32 local contexts: each old one-step effect agrees with the
new three-step effect. The gadget reads only offsets -1 and 0, so the untouched
exterior is arbitrary. Replacing one selector target causes 16 failures;
erasing the temporary tag causes 16 failures. These controls exercise both
origin selection and restoration of the overwritten scanned cell. They do not
establish anything about ZFC or about a complete blank-start synthetic program.

## Reproduction

Python 3 and a C++17 compiler are sufficient; no network, numerical solver,
Lean, or Rocq installation is required for this bounded search.

```
python3 verify.py --work /tmp/coordinated-marker-audit
python3 verify.py --work /tmp/coordinated-marker-replay --search
```

The default command decompresses the hash-bound invariants, independently
checks their closure, checks the source-table bindings and count arithmetic,
and runs the independent positive/mutation controls. `--search` additionally
compiles the delivered C++ source, reruns the synthetic discovery control and
all eighteen exact finite searches, and compares counts/hits with the saved logs.
The output directory must be fresh. Saved raw timings are incidental.
`code/local_invariants.py` is the inherited generator; an optional
`--regenerate` invocation recomputes its fixed points and requires byte identity
with each saved decompressed certificate.

## What this changes about the research direction

The searched family is more coordinated than one-state deletion or one-row
helper reuse: two pair identifications, a fresh selector, and both writes of a
temporary tape tag are active together. Its failure narrows that specific
family, while leaving source redesign, a different register/tape invariant,
changes to existing provider rows, nonlocal joins, and three-or-more-pair
sharing open. The search supplies no finite or universal lower bound on the
number of states needed for the consistency equivalence.
