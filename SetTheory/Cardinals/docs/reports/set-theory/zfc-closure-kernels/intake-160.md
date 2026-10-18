# Batch 160: a shared-carry 250-state machine

Sources 57–59 continue the machine-minimization spine of this report. The two
new 250-state submissions contain **the same transition table**. Their ordinary
proof and executable audits support a credible two-state improvement over the
maintained permutation252 machine. The exact-table Lean endpoint and the
equivalence formalized inside PA remain open. The active work now prioritizes
verification and formalization of this 250-state construction.

The reconciliation-note option preserves the base article and all delivered
text. No delivered article or PDF is rewritten. No source is superseded, and
the collection remains 290 reports, with 59 sources in this host.

## Provenance and preservation

| Source | Arrival / manuscript pin | Contribution | Placed / archive-only |
| --- | --- | --- | ---: |
| 57, prefix | `22bcfe0e05` / `43026ff42f0939f09b9e95495248cfadcad38e38` | Earlier phase-dependent prefix shift, MP0 source change, 252-state startup, rejected scanner fold | 485 / 3 |
| 58, carry | `126d12e470` / `a3f06a2059dd786ad385079106454efb84b87d3c` | Shared carry/rollback, spare invariant, pulse initializer, exact 250 table and complete audit | 51 / 8 |
| 59, audit | `6993a40aef` / `80e26b89e905bf3e5dfc322befdc1c6eaf25a109` | Same table, independent induction/marking/retiming audits, full-PC check, detailed set-coded calibration | 97 / 11 |

Placement `f7ba71df2d` preserves 633 ancillary files byte for byte from fresh
Git archive extractions. Twenty-two manuscripts, sections, PDFs and root
delivery READMEs remain recoverable from the committed arrival archives.
The [placement map](data/intake-160-placement.json) records every original and
shipped name. Flattened paths, including the few index-shortened filenames,
are reversible. Delivered scripts, audit notes and Makefiles still use their
original nested names; use the [recovery instructions](intake-160-reproduction.md).

The history check queried 568 unique payload blobs, finding 155 previously
seen blobs and checking 39 placement/merge commits in their own trees. No main
manuscript or constituent TeX had an earlier placement hit. This is an exact
payload/history check; checksum manifests were not interpreted or verified.
Scratch directory numbers 161 and 162 in frozen reviews denote working
directories, not additional intake batches.

Mira-Cult's original calculus and machine, Jeff Ketchersid's verification,
Andrew James Wade's compiler, mira-emmy's public 253-state reduction, ProveIt's
permutation252 and formal developments, and the earlier working prefix/pulse
research retain their attribution. The source-59 audit explicitly does not
claim discovery of the prefix/pulse idea or worldwide priority. The preserved
licenses and provenance files govern the imported material.

## Source 57: the predecessor and its limits

The earlier prefix-decrement routine enters state43 and requires the left
zipper `1^k ++ [0,0] ++ L` with `k ≥ 1`. Its positive branch emits an additional
one on that side. This phase premise is essential; an arbitrary-left-context
version is not justified. Its clean startup takes 25,612 steps, and its
rebased MP0 source has 8,366 guarded cases. The final table still has 252
working states. The retained original-engine MP0 initializer has an initially
unsafe cache frame and an explicitly checked later safe frame.

The MP0 source correspondence has 2,998 pairs and 5,994 edges. The extended
replay regenerates that relation from the pinned literal source before
checking it. Source-level AX/MP/DROP, constant-one NIP and projected-GEN
arguments are distinct alternatives; their bounded AX regressions use a zero
gate and do not establish the universal axiom-gate argument. Semantic proposals,
backend counts, failed reductions and incomplete searches retain their exact
scope in the [source review](intake-160-source-57.md).

This source also supplies a concrete refutation of an earlier **different**
250-state scanner fold. Redirecting the zero return through state3 produces
the wrong successor PC at source path `1110100100100000100`; the baseline takes
398 steps and the rejected candidate 486. The counterexample was reproduced.
It does not refute sources58–59, which keep the zero exit112, retain the
original 6,460-leaf program and use a different shared carry and initializer.

All twelve requested extended checks passed on a fresh copy, including 17,325
whole-tape positive-transfer regressions and the regenerated MP0 relation.
Completed/partial search records are supplied evidence unless the source
review explicitly identifies a fresh replay. No search failure is a state
lower bound, and no newly checked Lean endpoint belongs to this predecessor.

## Sources 58–59: the exact improvement

The canonical table has 250 working states, 500 rows, start0, dispatch92 and
separate halt250. Its SHA256 is
`0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e`.
The original-label table has start97, dispatch96 and halt254, with SHA256
`fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43`.
Both forms are byte-identical between the two submissions. Starting with
permutation252, remove states43,59,85, add255, and change seven surviving rows:

```text
30/1  -> 0 R 95
75/0  -> 1 R 255
75/1  -> 1 L 63
97/0  -> 1 R 83
97/1  -> 1 L 131
109/0 -> 0 R 75
131/0 -> 0 L 48
255/0 -> 1 L 97
255/1 -> 1 L 131
```

The original program and physical permutation `(6,2,0,4,3,7,8,5,1)` are
unchanged. No calculus rule is removed. Count the two submissions' common
6,460 leaves and 8,391 guarded instruction cases once.

Let `B(v)=0 1^(v+1)`, and let `width(A)=Σ(v+2)` over a finite register list.
From marked input `B(A)00 1^x B(R)` at file origin0, the three universal
contracts are:

| Operation | Complete result | Literal duration |
| --- | --- | --- |
| Positive decrement, `x>0`, entry95 | Exit48/head0, `1 B(A ++ [x-1] ++ R)`; new file origin1 | `2*width(A)+4` |
| Zero decrement, `x=0`, `R` nonempty, entry95 | Exit112/head−1; original plain file restored | `2*width(A)+7` |
| Increment, entry73 | Exit48/head−1; selected value increased, new value-one spare appended | `2*width(V)+7` |

The recurrent file has nine primary blocks and a **nonempty finite spare
suffix**. Spare values may be arbitrary naturals. Increment adds a spare and
the other operations preserve it, so the zero test always has a following
block. Physical spare blocks do not change the logical zero-tail registers.
The positive branch's extra boundary one must be included in the frame proof.

The marking routine uses 24 unchanged rows. Its complete-word induction
preserves arbitrary exterior contexts and has duration `2*width(A)+3`.
The independent induction checker establishes four one-block identities,
three macro identities and nine marking cases using unary and finite-list
induction. The word identity `C(A)1=1B(A)` has an explicit ordinary cons proof;
the Python flag enabling its use is not a proof-assistant kernel theorem.

The retiming compares an auxiliary carry circuit with the final machine at
states outside `{97,255}`. The only external entry is75/read0. For either probe
bit, three transitions have equal complete-tape endpoints; all other external
steps agree. The incoming-edge invariant forces every later visit to97 to
read1. Its read0 row is therefore available for the actual blank initializer.
This proves a general finite-run comparison, rather than extrapolating from
startup samples. The stronger audit checks arbitrary-exterior local identities
and 584,942 complete-tape cutpoints of the concrete startup.

After exactly 585,431 transitions from the actual blank start, the machine is
at old state96/head−3, with marker−4, header225, distance228 and empty PC.
Physical primaries are `[0,2,0,4,0,0,1,0,0]`, followed by 210 value-one spares.
There are exactly 438 one-cells; the complete support is recorded, including
both blank exterior tails. Logical values are
`(N,T,W,A,D,H,X,Y,L)=(1,0,0,0,4,0,0,0,2)`.

The full source parser consumes every token of all 6,459 source nodes and
checks tree coverage, register bounds and every leaf. The alternate full-PC
audit retains overflow and trailing zero cells. The invariant requires a clean
PC and **total head-to-header distance** at least40. Depth is at most34;
positive decrement and PC overflow increase that distance. This distinction
from an arbitrary fixed gap is needed to rebase every legal source onto the
checked cases. The minimum13 literal steps gives positive progress; the
reverse halting implication follows by strong induction on finite halting time.

The full-PC checker is an independent parser/PC/oracle audit but shares the
literal symbolic engine. It is not a second independent binary semantics
implementation. Independent literal regressions instead cover 33,564 complete
instructions (14,197,744 steps) and 16,200 macros (8,359,100 steps). These are
finite implementation checks, not the proof of the unbounded statements.

## Calibration and remaining formal work

The dirty root matches `Bisim254.prog254_halts_iff` and
`DirtyProgram254.six_nonformula_path_iff 1 0 4 0 0 2`: truth in the formula
slots and an empty stack discharge safety, while six numerical fields are
arbitrary. This uses the existing all-state theorem, not a newly assumed
zero-root theorem for the changed startup.

Source59's ordinary ZFC composition uses set-coded syntax and completeness,
the internally well-founded subdomain and the internal constructible
subdomain. It does not assume that a model of ZF is externally well-founded
or transitive. GIC ranges over first-order formulas with parameters. The
argument is specific to the inherited lemmas, not a generic translation of
Lean's universe theory into ZFC. Independent review found no fatal defect in
the reviewed argument; it did not rebuild the entire inherited calibration.

The existing `BinaryZFC252.nonhalting_iff_zfc_consistency` remains a checked
theorem about the **252-state table**. It does not certify the new table.
Formal work for250 must supply its literal table, unbounded operation contracts,
strengthened frame, regenerated site proofs, complete startup, and final
composition. Internal PA proof translation remains separate unfinished work.
The delivered ZFC-provability claim does not relax the user's PA target.

Unconditional nonhalting, consistency of ZFC, state minimality and a 249-state
solution are not established. Under consistency, Gödel's theorem rules out a
ZFC proof of the indicated nonhalting statement; full two-sided independence
requires an additional appropriate soundness assumption. Priority caveats and
all failed/unfinished alternatives are preserved.

The [mathematical review](intake-160-mathematical-review.md) and
[symbolic-checker review](intake-160-symbolic-review.md) give the detailed proof
boundaries. All source58 checks and all nine source59 checks passed on fresh
copies. Source59's nine regenerated substantive JSON records match delivery,
except for three timing fields. Source58 differs only in timing and relocated
path metadata. Neither replay invokes a proof assistant. Fresh evidence is
listed in the [reproduction note](intake-160-reproduction.md).
