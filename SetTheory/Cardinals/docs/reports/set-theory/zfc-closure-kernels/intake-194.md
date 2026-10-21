# Batch 194: a second presentation of the same 217-state machine

Commit `673c87a878` does **not** supply a different state saving. Its entire
source is byte-identical to Source 152, and its binary machine is exactly
isomorphic under a three-state permutation. It also exactly matches the
independent candidate025 already published with the primary construction.
The two reductions therefore cannot combine to reach 216. The current
[primary 217](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k217/README.md)
remains unchanged. The [new presentation and comparison](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k217/presentations/exposed-marker/README.md)
are retained for readers who prefer its breadth-first state numbering.

## Exact comparison

The direction of the native relabeling is **new submission → accepted primary**:

| New native state | Accepted native state |
|---:|---:|
| 188 | 213 |
| 213 | 210 |
| 210 | 188 |
| Every other state, including initial 0 and halt 254 | Itself |

The independent reader checks the write bit, move and mapped destination for
**all 434 rows**. It also checks both complete canonicalization maps and
all 434 canonical rows. A bijection on states gives an immediate step-for-step
conjugacy on every tape and head position: only the state name changes.
In particular blank halting, the complete startup and all source behavior
are the same. This is stronger evidence than matching state counts or running
the two machines for a finite number of steps.

The source contains exactly the same 4,751 ordered leaves, all addresses,
203 distinct subtrees, depth 45 and zero-run 6. All 4,750 internal-prefix
roles agree under the permutation. The new native and prefold tables and
source are also **byte-identical** to the independent candidate025 retained
in the primary's research publication. The comparator discloses that its
author also authored that independent reconstruction; its literal-row parser
imports no delivered constructor/runtime code.

| Artifact | Accepted Source 152 | New Source 155 |
|---|---|---|
| Native SHA-256 | `b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088` | `c902a3c5e81176230a2213d631e2e691573c167fb03e9bdb09ef5c88154f3099` |
| Source SHA-256 | `9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655` | Identical |
| Compact-state ordering | Sorted native labels | Breadth-first, zero edge first |
| Compact dispatcher label | 83 | 23 |
| Retained-row edits relative to the same dominated K218 parent | 9 | 6 |

The six-versus-nine edit count measures how state labels line up with the
parent; it does not change the number of states or transitions in the final
machine. Both use the same reassociation of five closed factors of lengths
14, 27, 53, 374 and 3,682, changing 94 source addresses. The useful helper
is named 188 in the new table and 213 in the accepted one. Both delete 400
by sharing 69 and reading the predecessor marker immediately left of the
head. The scanned-one branch takes one step; the zero branch takes three,
restores both cells and reaches the old endpoint. Closure and absence of
halts do not imply termination of a factor; equal guarded control graphs
preserve possible divergent executions too.

## Useful additional material

The manuscript gives a compact direct four-row prefold construction and an
independent four-case fold audit. Its relative proof is valid from state 0
on every initial binary tape, using the unique incoming writes to 69 and
400. It does not assume the marker at an arbitrary externally supplied
configuration inside the merged pair. There are 432 other mapped rows;
positive one/three-step blocks give both halting directions without hidden
infinite stuttering. The new top-level proof inherits Source 149's exact
numerical domination and cofinal common-input compiler; it introduces no
stronger theory or different consistency assumption.

The separate **fixed-label nonlogical core** is useful theory/source research.
Let `N(X)=I(X,1)`, `V(a,b,c)=I(R(a,b),Q_c R(a,b))`, and let `J(a,b,c)` be the
exact inherited `nks222` term. Replace the old bundle `N(I(V,J))` by:

- All `V(a,b,c)` with both original gates `c≠a` and `c≠b`.
- Only `N(J(1,3,c))` with `c≥4` as the nonlogical core.

Keep truth, MP, theorem-only GEN, rho1–rho6, merged G and unrestricted rho8,
or the independently calibrated dominated replacement. This calculus is
ordinarily proved equiconsistent with ZFC; equality of every old theorem
code is not claimed.

For the upper translation, old bundle projections derive each new clause.
For the lower translation, the inherited propositional/equality developments
use no bundle. The only bundle use in the interpretation supplies general
fresh membership vacuity, now available directly. The remaining lower-proof
use is `Q_seed` at labels 1,3, with `seed_code(phi)>3`. From the required V
and `N(J)`, assume `I(V,J)`, derive J and then 1 by MP, and discharge the one
assumption using the K/S deduction transformation. This reconstructs the exact
old bundle without GEN under an open assumption. The retained named-seed and
ZFC-to-K0 transfer then apply. Reviewed module excerpts support this ordinary
adaptation; no Rocq/Lean theorem was newly compiled.

This overlaps earlier fixed-role work: Source 145 already considered general
V plus a core at labels 0,1; Source 154 supplies an explicit renamed lower
environment and the separate false-code roles 1,8 refinement. The new appendix
uses **the existing lower proof's labels 1,3 directly**, with `c+4` avoiding
collisions, and supplies exact symbolic emitter reconstruction. It retains
both gates on V. Its exploratory 0,1 source files do not themselves supply
the missing lower-proof renaming; the earlier ordinary result can be cited
separately without implying a complete compiler for those literal sources.

| Exact source experiment | Distinct subtrees | Leaves | Depth | Zero run |
|---|---:|---:|---:|---:|
| Accepted dominated source | 203 | 4,751 | 45 | 6 |
| Fixed 1,3, direct; private code c+4 | 211 | 4,718 | 46 | 9 |
| Fixed 0,1, direct; private code c+2 | 210 | 4,673 | 46 | 9 |
| Fixed 0,1, reassociated | 210 | 4,673 | 47 | 6 |

These are **source-subtree counts, not TM state counts**. The source emits
`N(J(1,3,c+4))` and then gated V at the closed interval [2657,4570), under
the inherited all-natural macro contracts. It adds a formula to AX's stack;
a complete revised command-block compiler is still missing. The direct
zero-run 9 also exceeds the existing decoder's six-zero condition. No binary
allocation, startup or universal runtime is claimed for these experiments,
and none improves the accepted source's 203 subtrees.

## Fresh checks and inherited proof

All three selected jobs pass in a disposable copy, each with a 60-second
cap; combined child time was 1.796 seconds:

| Fresh job | Scope |
|---|---|
| Deterministic construction | Four exact rebuilt artifacts, closed factors, whole primitive word and both guarded CFG readers |
| Independent four-case fold | Four exact two-cell cases, 432 mapped rows and rejected corrupt-initial-halt control |
| Fixed-core emitter | Exact 211/210/210-subtree sources, symbolic formulas, closed splice and two CFG readers |

[Actual commands and outputs](data/intake194-fresh/actual.json),
[independent semantic-result audit](data/intake194-fresh/review/actual-review.json),
[ordinary source/code review](data/intake194-fresh/review/review.json), and
[complete isomorphism receipt](data/intake194-fresh/comparison/review.json)
are separate records. The fixed-core execution omits only its initial
provenance-manifest loop in a retained adapter; every mathematical assertion
remains unchanged. The original script and exact diff are preserved.

No full runtime, startup, inherited logical proof, omnibus wrapper or proof
assistant was rerun. The accepted Source-152 evidence already supplies 6,176
arbitrary-natural cases, 1,616,558 symbolic rules, every row, minimum duration
13 and complete 312,617-step startup. Exact state conjugacy transports the
machine semantics. The new archive's own runtime/startup records are retained
as **delivered evidence**, not counted as another fresh execution. The
ordinary ZFC consistency equivalence is unchanged. A new exact-table Lean or
internal PA endpoint, unconditional nonhalting and minimality are not claimed.

## Intake, attribution and recovery

`K217_Exposed_Marker.zip` arrived at `673c87a878`, inspected repository pin
`704b87442afbd571833a628cd558f1d207fd8b2f`. Its immediate predecessor is the
exact dominated-rho8 Source-149 archive, whose own pin is `f8ec6158f3`.
Placement **`7fff7bc909`** retires the ZIP and accounts for all **57 members**:
31 new files (four root, eight code, 19 data), 20 existing aliases, one
historical parent archive and five archive-only article/PDF/delivery members.
The longest Windows-prefixed new path is 146. The host has **155 sources**;
the collection remains **290 reports**. Three later arrivals are separately
queued: `6ec69081ca` for batch 195 and two reports at `d3d6b8c14e` for 196.
The latest user goal is now 215 states or fewer.

[The map](data/intake194-placement.json) binds every original and alias to
its committed bytes, with introduction-tree provenance. An own first placement
check compared alias working-tree bytes and failed; the corrected check uses
the committed original bytes and requires no working diff. Both versions and
the failure record remain under `data/intake194-fresh/placement-history/`.
There was no checksum-manifest validation, line-ending inspection or
normalization. All supplied files remain unchanged; original-layout paths
and historical runtime commands in them remain historical data.

The report's independent exposition, audits and fixed-core refinement retain
their own attribution, together with Mira, Jeff Ketchersid and contributors,
Elliot Glazer, Andrew James Wade and ProveIt ancestry and original licenses.
This intake claims neither a new state-saving discovery nor priority over the
already published independent candidate025. [Recovery and selected reproduction](intake-194-reproduction.md)
restore the full original article, PDF, all evidence and the source appendix.
