# Batch 189: useful results from two unsuccessful 218-state searches

Sources 145 and 146 are the research arrivals `253b3ff50e` and `f8ec6158f3`,
respectively. Both predate the accepted [K218](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k218/README.md)
and pin K219 at `26d5de6d21fa354d50e0b84fe851c289925b8d72`. Their useful results
are retained: alternative 219 layouts, consistency obstructions, broader
initial seeds and enumeration schedules, and complete accounts of failed
encoding attempts. Their titles describe a historical target. Neither supplies
a verified machine with at most 217 states; Source 144 remains the primary.

## Placement, provenance and verification

Placement **`d134378a07`** accounts for all **1,036 members** and retires both
ZIPs in the same commit. The [map](data/intake189-placement.json) records 883
new files, 83 existing aliases, 45 batch aliases, two historical predecessor
archives and 23 archive-only article/PDF/input/delivery members. The new files
are 34 root records, 161 code files and 688 data files, with maximum
Windows-prefixed path length 159. Every member is recoverable in its original
layout. The host has **146 sources** and the collection remains **290 reports**.
The new contextual K218 arrival `3c7c3aa5a3` is separate batch 190.

Both are additions to the existing finite-refutation report, using its
reconciliation-note procedure. Attribution remains with the ProveIt research
contributors and their acknowledged ChatGPT-assisted work; predecessor notices
and licenses remain bound by exact aliases. No priority claim is added. The
host article and existing labels remain unchanged. Main manuscripts and their
proof inputs remain in Git, rather than being discarded after ZIP retirement.

The [independent ordinary review](intake189-source-review.md) reads both main
manuscripts and all substantive supplements. Its [receipt](data/intake189-source-review.json)
and [inventory](data/intake189-read-inventory.json) distinguish mathematical
proof review from delivered numerical evidence. No mathematical blocker was
found. The selected fresh checks are:

| Artifact | Fresh checks | Result |
| --- | --- | --- |
| Source 145 rho6 layout | Closed-subtree change, exact source/binding/canonicalization, two startup simulators, full generic runtime | 6,167 cases; 1,516,088 rules |
| Source 145 inert-insertion layout | Reachable zero guards, graph contraction, binding/canonicalization, two startup simulators, full generic runtime | 6,175 cases; 1,508,163 rules |
| Source 146 alternative219 | Own literal instruction-word comparison and complete blank startup | 312,617 steps; exact accepted 277-cell support |
| Source 146 initialized core | Own exact three-row/deleted-state comparison and 85-step blank trace | Proved outward zero-ray premises |

All five selected Source 145 jobs pass; the two full runtimes take about
144 and 146 seconds. Exact case arrays reproduce the delivery. Both startups
reach native state 84, head −5, header 139, gap 80, registers
`[3,0,0,0,3,0,0,0,0]` and 130 spares of value one after 312,617 steps.
The [actual record](data/intake189-fresh-state-search/actual.json) and
[review](data/intake189-fresh-state-search/review.json) bind those executions.
This runtime driver does not expose a row-use inventory, so no additional
all-row-coverage claim is made. Source 146's full generic runtimes remain
**delivered evidence**, not a fresh execution in this batch. The own finite
[audit](data/intake189-literal-check.json) states its narrower scope explicitly.

See the [reproduction guide](intake-189-reproduction.md) for exact selected
commands. Execution used copies. No omnibus wrapper, checksum manifest,
ancestor suite or proof assistant was run. An initial placement commit guard
objected to whitespace in unchanged delivered code/logs; it was removed for
those verbatim payloads, with no content rewrite. Its [record](data/intake189-placement-guard-note.json)
keeps this procedural correction separate from mathematical checks.

## Source 145: two layouts and stronger theory obstructions

The first layout changes the nongated rho6 family from `D(a,c)` to `D(a,b)`,
where `D(i,A) = Ex_i(Q_i A) → A`. Independent parameters still range over
exactly the same axiom set: old `(a,b,c)` maps to new `(a,c,0)`, and new
`(a,b,c)` maps to old `(a,0,b)`. This is equality of ranges, not equality of
individual emitted batches. Two closed 26-instruction pushes change four
register operands at ordinals 966, 971, 1144 and 1149. The physical changes
are only `199/1 = 1 R 12` and `206/0 = 0 R 76`.

The second layout inserts six primitives at `[4597,4603)`. A zero/positive
abstract invariant proves registers 7 and 4 zero at entry. Only two zero
branches execute; four inner instructions are unreachable. Contracting these
two identity steps preserves all outside guarded edges. The invariant and
termination of the inserted block are essential. The fresh closure computation
processes 19,820 work items and the contraction checks 6,166 outside edges.
Both layouts have 206 source subtrees and 219 working states; their instruction
counts are 4,744 and 4,750. They are distinct from Source 141's alternatives.

A specialized halting test has an ordinary source proof: its second comparison
register is zero, so test whether the first is exactly one by a preliminary
decrement and the shared equality routine. The attempted allocation overwrites
protected arithmetic row 38/0 and fails a concrete CI5 interface. Its repair
search covered **876 working-target actions**, not the 880 including halt
claimed in an ancillary SEARCH_REPORT. The retained code, log and main report
support 876. Original bytes are preserved. Two six-leaf alternatives also have
source proofs but worse sharing, with 208 subtrees. None is a valid smaller TM.

The theory appendix gives a full **ZFC-constructed two-world HC model** for
replacing rho6 by `Q_i A → A` alone. Future membership includes reflexivity
and colored antichain edges; uncountable fibers force the subset test to be
object equality. Countable closure supplies the literal seed bundle, including
coincident public variables and its repeated binder. Falsity is true at the
future world and false at the root. Thus this weaker calculus has consistency
provable in ZFC. Adding explosion invalidates this model; no such conclusion
is inferred for T plus explosion.

The four-value outer-head obstruction excludes an infinite family of fourth
inputs to rho8. At its two bad unrestricted valuations the fourth input must
have value 2; implication, quantification and equality roots avoid that value.
The model and structural induction supply the unbounded result, beyond a
finite formula search. It does not cover arbitrary membership terms or a different axiom basis.

Fixed public labels 0 and 1 with private label `c+2` do preserve consistency
strength when the **full vacuity component** and classical basis are retained.
The proof uses universal closure and capture-avoiding renaming at the stage
where those rules are available. One-fixed-label and predecessor-private
variants handle exceptional small-code collisions separately. Their measured
emitters are larger; shorter logical descriptions are not state savings.

The packet also retains bounded local synthesis, weak endpoint and source
bisimulation screens, product/joint abstractions, liveness analyses, physical
rotations, occurrence-local grammar search and equality synthesis. The finite
families, missing intermediate enumeration layer and timeouts remain scoped
as reported. Their negative results establish no arbitrary-machine lower bound.

## Source 146: a useful core with a proved startup failure

The initialized core deletes native 301 and changes `87/0` to `0 R 88`,
`88/0` to `0 L 51`, and `51/0` to `0 R 122`. A preceding source bit separates
two decoder roles. Its supplied generic runtime covers 6,167 cases and
1,515,192 rules, with all 436 rows and minimum duration constant 13.
The source remains the exact accepted K219 source. This is an initialized
runtime result, with no successful blank initialization.

The failure is exact. At step 79, state 51 scans cell 5 with ones only at
−3 and −2; its right neighbor is zero, violating the local helper premise.
At step 85, state 35 scans cell 7 with the same support, and `35/0 = 1 R 35`.
Induction gives an infinite writing ray. The own finite audit freshly confirms
the patch, complete prefix and ray premises. This core is unconditionally
nonhalting from blank and cannot be adopted as the consistency machine.

The packet's separate alternative219 changes 35 rows and has a different
source layout. Its delivered full runtime has 6,167 cases and 1,512,606 rules.
Our finite audit confirms the identical instruction word and its complete
312,617-step startup; its supplied complete source/runtime certificates remain
separately identified. Its larger count does not replace K218.

The **general clean-seed theorem** permits any complete root frame with
`[n,0,0,0,d,0,0,0,p]`, for natural n,d,p. Soundness needs theoremhood of the
formula/cache/stack entries; their zero values satisfy it. Completeness uses
a uniform reset prefix and the cofinal successful-code family
`N_U = P(3,P(1,P(1,P(U,R))))`. An initial proof list drains before the ordinary
candidate enumeration resumes. Arbitrary dirty theorem registers and incomplete
physical frames are not allowed, and old seed-specific invariants do not
transfer automatically.

More strongly, four nested Cantor pairings give
`v₂(N_(U+16t′) − N_(U+16t)) = v₂(t′−t)` for `t′>t`.
Thus successful padded refutations are cofinal in **every residue class modulo
any fixed power of two**. A scheduler that drains each proof list and visits a
fixed progression with stride `2^k` remains complete. Variable strides are not
covered. This gives useful freedom in designing an initializer, but supplies
no initializer or machine reduction itself.

The fused row `NN(Q_i A) → A` is equivalent, over retained classical rho8, to
T plus explosion. Its 211-node proof certificate and three displayed deductions
are retained. Equiconsistency of this replacement remains open. It differs
from the newly [calibrated K/S + QS theory](../../../../../../Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/README.md),
which adds `NN(Q_i A) → Q_i A` **while retaining rho6**.

The second HC T-only countermodel is a different proof: future membership is
membership-or-equality, and its subset condition leaves countably many witness
requests. It also handles the specified raw dual replacement, but not T plus
explosion. A separate T+EXP countermodel is relative to an assumed model of
the original theory; it proves nonderivability of rho6 under that assumption,
not a ZFC-internal consistency reduction.

For the stated constant-domain relational semantics, a nontrivial terminal
strongly connected cluster yields a model of the original theory: V and G
make atomic interpretations constant, then structural induction makes all
formulas constant and quantifiers become ordinary universal quantification.
No transitivity assumption is needed. A representation/completeness theorem
for the altered calculus and an argument ensuring such a cluster are missing;
infinite frames without terminal clusters are not excluded.

Further preserved contracts include a calibrated G/H implication basis, the
safe contradiction target of **any proved membership atom**, and an all-left
cancellation/reset equality routine whose loop decreases a natural sum. The
latter clears both inputs and has the right return/break behavior, but loses
existing sharing and needs an unsupported right-CI6 entry. Source/node costs,
partial interface checks, pair reversals and register transports are not
complete binary-machine theorems.

Two startup repairs reach clean frames but corrupt ordinary CD8-zero behavior.
All 24 tested top-level phase orders, selected loader reorderings, expanded
radius-10 local families and 3,386,880 transported start configurations are
retained with their exact proof boundaries. The eight-row searches that timed
out remain incomplete. None is promoted from a bounded pass to a theorem.

## Present implications

The three archived membership-fourth proposals formerly described as open are
now excluded by the repository's [six-orientation obstruction](../../../../../../Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/six-orientations/README.md),
for each fixed orientation separately. That earlier proof did not cover a union
of different rows; [Source 147](intake-190.md) now supplies a five-value matrix
that does. These historical conditional sources are not calibrated contenders.

The generalized seed and fixed-stride results offer the clearest new freedom.
The intake's later [217-state all-start audit](../../../../../../Computability/BusyBeaver/Research/ZFC/k218-continuation-search/README.md)
proves that merely choosing another existing initial state cannot repair the
specific delete301 stack on accepted K218: every start reaches a blank ray.
A successful use of the new seed theorem must therefore change more than its
initial-state label. Other open routes are a new halting-test allocator,
actual-helper pricing of the all-left comparator, and calibrated parameter
changes combined with a new decoder layout. No new Lean endpoint or ≤217-state
result is claimed by this intake.
