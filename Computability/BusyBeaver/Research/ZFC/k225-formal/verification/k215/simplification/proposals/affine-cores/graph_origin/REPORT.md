# Replace explicit source correspondence with canonical ordinal graph equality

## New result

The two actual pinned Lean decoder trees `KSource215.t215` and `KSource215.tD`
have the same canonical, increment-weighted test graph. This is not a graph
isomorphism guessed by search: the correspondence is the identity on the
left-to-right ordinal of each primitive leaf.

An independent new parser/checker established:

- Both trees have 4,751 primitive leaves.
- Both have 1,425 decrement-test leaves and one halt leaf: 1,426 graph vertices.
- There are exactly 2,850 labelled successor edges, one zero and one nonzero
  edge per decrement-test vertex.
- Both edges at every vertex have the same next-test ordinal and the same
  increment-count vector. Both initial segments also agree.
- Every one of the old 2,240 pointer pairs normalizes to the SAME leaf ordinal
  in both trees. Only 1,426 distinct ordinals occur: 814 records are aliases.
- Every incremental/control segment uses at most five source transitions, and
  each side has 3,420 such transitions summed across its 2,850 edges. The
  initial segments have length zero. A reflected segment evaluator needs at
  least six units of the current `seg` fuel to include its terminal inspection.

The source proof can therefore be expressed as:

1. Compile each concrete tree to its canonical weighted test graph.
2. Kernel-check equality of the entire resulting graphs, including initial
   data, labels, both successors and increment vectors.
3. Apply ONE generic graph-adequacy/graph-equality theorem.

This removes the explicit 2,240-record correspondence altogether, not merely
its reverse or its zero offset field. No source transformation theorem for this
particular K215 program is required once generic adequacy is proved.

**Verification status:** these are independently checked finite-data results,
not newly compiled Lean/Rocq theorems. The proposed adequacy theorem below is a
precise mathematical design. Neither it nor the proposed normalized checker has
been implemented and compiled in a proof assistant here.

## Exact semantics and proof obligations

Let T be a finite decoder tree. Reject `.none` and `.node` as leaf instructions,
and enumerate all actual primitive leaves in left-to-right order. Store the
full root-to-leaf bit path q(o) for each ordinal o.

For any pointer P, `tsite T P` first traverses T with implicit trailing zero bits
and ignores any unused suffix beyond the leaf. If it returns `(e,Q)`, Q is the
FULL consumed path, not necessarily P. Define `canon_T(P)=ordinal(Q)`.

A prerequisite lemma proves: if `tsite T P = some(e,Q)`, then
`tsite T Q = some(e,Q)`. For every register file R, executing from pointer P or Q
therefore yields the same next configuration, because existing `step_tsite`
uses `execute e Q R`. Their halt tests also agree. Thus canonicalization merges
only control pointers with exactly identical next-step and halt semantics;
it does not identify source subtrees by syntax or ignore ancestor effects.

Define a segment evaluator with an explicit finite fuel. It performs only
`inc`, `brk`, and `cont` steps, starting from an arbitrary pointer. At `decnz`
or `halt`, stop. A successful result contains the next canonical ordinal and a
finite register-increment vector. Reject exhaustion, failed lookup, or malformed
instruction. The implementation may accumulate a list of increments and convert
it to a canonical finite map or a nine-entry vector after checking register
bounds. A segment performs no decrements and no register tests; increments
commute, so the vector determines its action for every natural-valued register
file. Existing `seg_run` and `seg_hn` give almost all of this proof already.

For each decrement leaf `(decnz r,Q)`, compile:

- The zero edge by running a segment from `breakPath 1 Q`, without changing R.
- The nonzero edge by running a segment from `incPath Q`; executing this macro
  first decrements R[r], then adds the segment's increment vector.

For the unique halt leaf, emit `halt` with no outgoing edges. Include the result
of a segment starting at the empty pointer as the graph's entry descriptor.
A successful compilation checks ALL test vertices, not just those observed in
bounded executions, and both outcomes even if one seems unreachable.

### Generic adequacy theorem

If `compile fuel T = some G`, then for every natural-valued register file R,
source execution from the empty pointer halts iff G, begun at its entry ordinal
with its entry increment vector added to R, reaches a halt vertex.

Proof: every graph edge expands to the actual decrement step followed by the
finite certified segment, with exactly the stated register update. Conversely,
every source execution beginning at a graph checkpoint must take the matching
zero/nonzero branch and follow that deterministic finite segment; the segment
contains no hidden test or halt. Canonical aliases have identical semantics by
the prerequisite lemma. Concatenate these macro expansions for one direction;
for the other, induct on a finite source halting derivation or use `seg_hn` to
consume each segment and the preceding decrement step.

Each nonterminal graph step consumes at least one source transition: its
initial decrement test. This supplies strict progress even when its following
segment is empty. The initial segment may be empty and needs no positivity.
A successful compiler cannot hide an infinite control-only loop, since that
would exhaust fuel rather than return a graph edge. None of this assumes the
register loop terminates or assumes consistency/nonhalting of the machine.

### Equality theorem

If both compilations return exactly the same G, their source halting predicates
are equivalent from every register file. This preserves the existing theorem
`KSource215.p215_halts_iff` and therefore all downstream K215 endpoints and their
assumptions. Equality is a fully evaluated structural Boolean check proved sound,
not equality of hashes and not an imported Python assertion.

An even smaller proof addition avoids constructing a second operational graph
semantics: define the existing `RMBisim.Bisim` relation by equality of canonical
checkpoint ordinals. The graph equality facts establish its start and step
fields directly, with the existing segment lemmas. Invoke the ALREADY PROVED
`Bisim.halts_iff`. This reuses the current symmetric simulation theorem rather
than proving another halting framework from scratch.

## Important correction: literal-pointer checker cannot simply reuse canonical data

`RMBisim.seg` returns the RAW pointer at the stopping checkpoint. The existing
`branchOk`/`obranchOk` compare that raw pointer literally against certificate
pointers. They do not normalize it via `tsite` first. The old duplicate entries
partly accommodate these aliases.

`CanonicalCert215.lean` demonstrates the 1,426-entry normalized correspondence
in 126 KB, but is DATA FOR A PROPOSED NORMALIZING CHECKER, not a certificate for
the unchanged checker. The independent audit finds 5,324 endpoint-side raw
pointer comparisons (out of 5,700) that need canonical normalization. This is
why a naïve deduplication fails, despite exact graph equality. The generic alias
lemma and normalization-aware relation above are essential.

The canonical table is a transitional option. The final graph-equality approach
can dispense with it entirely: ordinal labels are computed from both trees.

## What the actual structural changes look like

The ordered primitive words are not identical: 855 positions differ. They are
exactly 343 changes `cont3→cont2`, 175 swaps of adjacent `inc7/inc6` pairs, and
81 swaps of adjacent `inc1/inc6` pairs (512 increment positions in all).

Intersecting the trees' leaf-interval families yields 8,892 common intervals.
A syntactic skeleton audit identifies a small repeated family:

- 175 three-leaf rotations combining `inc7/inc6` commutation and `cont3→cont2`.
- 81 analogous rotations for `inc1/inc6`.
- 87 rotations of two larger body blocks, again with `cont3→cont2`.
- 81 reassociations of four increments of register1.
- Two other four-block regroupings, one six-block regrouping, and one large
  AX-chain reassociation skeleton.

These counts are a SYNTACTIC decomposition, not independently proved rewrite
rules. It would be unsound to prove unrestricted associativity for these trees:
`brk` and `cont` refer to enclosing context. A structural rewrite compiler would
need an interface of all normal/break/continue exits and prove matching exits
under the new context, including the adjusted continuation depth. Bare equality
of subtrees or increment multisets is insufficient.

The canonical graph route is safer and simpler here: it computes those exact
context-sensitive targets for every occurrence before comparing the graphs.
It captures all recurring rotations without requiring a large collection of
specialized context-congruence lemmas. A later verified closed-block compiler
could remove repeated traversal too, but that is a separate, higher-risk
optimization and is not needed to eliminate the explicit correspondence data.

## Honest cost claims

The forward certificate data alone occupies about197 KB in the current Lean
source; its mirror repeats about197 KB. The graph approach needs no generated
mapping data. Sixteen forward check modules (and, before symmetry, sixteen
backward modules) can be replaced by the new graph-equality proof checks.
This does NOT mean their computational obligations disappear: both trees must
still be compiled and their full graphs compared under the kernel.

Canonicalization reduces semantic checkpoint cases from2,240 to1,426 (36.34%
fewer) and rejects redundant aliases at the representation boundary. The old
forward check workload was1,087.66 compiler seconds in the published successful
build record. No timing saving for the new checker has been measured. Path
lookup, expansion of the long reference tree, graph construction and equality
could dominate; graph computations should use indexed structures and be
partitioned/benchmarked before claiming improvement.

The longest full leaf path is47 bits in the source and178 in the reference.
The old paired checkpoint codes reach176 bits; there is no contradiction since
noncheckpoint leaves may be deeper. An ordinal graph avoids binary-coded-pointer
fuel issues altogether once the finite tree traversal is proved correct.

## Reproduction and source pin

Run, using Python3 standard library only:

    python inspect_trees.py
    python check_ordinal_segments.py

The scripts parse inert Lean literals; they never import or execute repository
code. `SOURCE_PINS.json` pins commit, path, exact size and Git blob SHA. The
materialized `upstream/` sources were checked against those Git blob identities.
`ORDINAL_GRAPH_AUDIT.json` is the compact result. `ordinal_graph.json`,
`leaves.json`, `trees.json` and `motifs.json` preserve inspectable data.

Commit: c9dc79323429112c698100f3226a6e4d56c8b782.
Source:
https://github.com/VladimirReshetnikov/ProveIt/blob/c9dc79323429112c698100f3226a6e4d56c8b782/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean

No remote repository changes or pushes were made. All reported graph checks are
ordinary independent finite-data checks, not proof-assistant certification.

## Independent-review correction retained

Root review caught an initial error in the owned Python increment helper: it
inserted a leading1 on all-ones overflow. Actual `incRev []=[]` wraps without
length extension, including empty→empty. The helper was corrected and the FULL
graph, alias, canonical-data and segment audits rerun successfully. All reported
graph counts/equalities remained unchanged. The script now tests all2,047 bit
strings of length0–10 against a separate literal recursive transcription of
`incRev`, including explicit empty and all-ones regression cases. This correction
is not hidden and reinforces that the Python result is not a kernel proof.
