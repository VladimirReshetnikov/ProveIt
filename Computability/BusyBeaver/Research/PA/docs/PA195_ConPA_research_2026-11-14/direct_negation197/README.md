# Direct negation on the separated diagonal / Combined196 program

This is an **experimental 197-state binary machine**, not a solution of the
requested below-196 problem. It implements a 3,433-site register program,
shortening the 3,649-site separated diagonal / Combined196 source by 216
sites. The shortening does not reduce the physical state count.

The native transition table starts in label 74 on a two-way infinite zero
tape; label 254 is the unique terminal label. Native labels are sparse. There
are exactly 197 working labels and 394 transition rows, and every working
label is graph-reachable from the start. Native table SHA-256:

`7ec16667602edb3580d682614d45299d6ef8f324331d940395a84b563f5c2a0d`

`machine.tm` is a dense, start-at-zero relabeling with working states 0..196
and halt label 197. `labels.json` records the dense-to-native bijection.

## What changed

At each of eight occurrences, replace the 47-site block

    push; increment T; cons

by the 20-site block

    drain T into S; increment T; pair-and-multiply-by-four

with existing native entries 28 and 106 for the first and last macros.
Here T=r1, W=r2, S=r6, R=r7. If R=0 on entry, both blocks terminate with

    (T,W,S,R) = (4*pair(t+s,1), w, 0, 0)

when the initial tuple is (t,w,s,0), leaving every other register unchanged.
The Cantor pairing is pair(a,b)=triangle(a+b)+b. Thus each block computes the
same negation code, including the effect of an arbitrary initial S. The
zero-scratch precondition is required; see proof.tex.

## Verification evidence

Run, using Python 3.10 or later and only the standard library:

    python3 replay.py

The deterministic audit checks all of the following:

* All eight old blocks have the same 47-site control-flow graph and all eight
  new blocks the same 20-site graph; no external edge enters their interiors.
* All 3,273 source rows outside the replaced blocks agree after ordinal
  relocation, including every decrement branch and every jump.
* Independent arithmetic-path and interval-based source resolvers agree.
* Closed zero/positive abstractions from the actual clean seed contain
  263,244 old and 247,308 new site/mask pairs. Every negation entry forces R=0.
* The whole candidate passes 4,461 symbolic primitive-runtime cases. These
  cases carry an affine tape gap and an arbitrary complete register file;
  they call the upstream arithmetic block interfaces for the unchanged
  register operations. The largest case takes 497 symbolic steps.
* The literal blank startup reaches the exact source seed after 57,922 steps.
* The five simultaneous reader folds pass the local finite simulation check.

The arithmetic macro proof is in proof.tex. The executable symbolic checker
is a certificate relying on the stated upstream block contracts; it is not a
new Lean or PA kernel theorem. This package does not assert a newly verified
end-to-end PA consistency biconditional.

## Source provenance

The parent combines the separated diagonal axiom emitter in
`docs/incoming/pa_consistency_comparison_and_new196_2026-11-13.zip` with the
Combined196 MP/scanner changes in
`docs/incoming/conpa_tm_study_2026-11-13.zip`, as pinned in ProveIt commit
`906367250a7f96c923147b10df392294bced7be5`.

`code/reference` preserves the upstream PA196 program, conjugacy and literal
table used by the imported checker. `code/parent.py` records the exact six
native row edits and the two source-tree changes defining the Combined196
control part. The separated diagonal numerical calculus is unchanged by the
negation rewrite. Original license notices are retained.

`best.grammar.json`, `parent.grammar.json`, `word.original.json`, the native
and dense tables, `sites.json`, `folds.json`, and `audit.json` are the complete
replay inputs and outputs. The bounded search additionally tested all 1,280
selected subset/layout combinations and three 180-second anneals from the
good 197-state layouts. None yielded a table below 196 states. These finite
negative searches are not lower bounds.
