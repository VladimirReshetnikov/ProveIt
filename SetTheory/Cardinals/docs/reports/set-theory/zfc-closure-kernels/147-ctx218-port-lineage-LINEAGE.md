# Deterministic construction from upstream K219

Run, with Python 3.9 or newer and only the standard library:

    python build_lineage.py --out rebuilt_all

The command is independent of the working directory. Optional
`--upstream-table` and `--upstream-source` accept explicit input paths, but the
same pinned SHA-256 hashes are mandatory. Optimization mode is rejected because
the separately maintained downstream byte constructor uses assertions.

## Input and output identity

The input is the native K219 construction from upstream commit
`26d5de6d21fa354d50e0b84fe851c289925b8d72`:

- Table: `b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`.
- Source: `0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789`.

Native labels 301 and 302 are bijectively renamed to 102 and 120 during the
construction. The exact native input is recovered under the inverse map. This
renaming changes neither states nor tape behavior. The final native output
reverses this map; state 79 is an additional ordinary working label.

- Final normalized table: `4dd4ca3893a80b99a1df52e4a57f0357eeb697255f86f43b859a1a97ef511651`.
- Final native table: `3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1`.
- Final source: `1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe`.

## Stages and exact state accounting

1. **Normalized upstream:** 219 working states, 438 transition rows; 206
   distinct source-DAG nodes, comprising 183 binary interiors and 23 primitives.
2. **startup37 reparse and allocation:** 219 states. Its explicit source grammar
   has 205 nodes, comprising 182 interiors and the same 23 primitives. All first
   37 initialization addresses are unchanged. The physical allocation changes
   exactly 55 retained table rows; no physical label is added or removed.
3. **Single-role188 reparse and allocation:** 220 states. The second explicit
   source grammar still has 205 nodes. The physical allocation adds state 79
   with its two rows and changes exactly 46 retained rows. This is a temporary
   construction stage, not an asserted reduction by itself.
4. **Direct188:** 219 states. Delete both rows of 190 and replace only
   `188/0 = 0 R 165` and `188/1 = 1 R 20`. All five source occurrences of 188
   now use one logical source role. The two new rows are literal one-step
   child-entry identities on arbitrary tapes, without a left-context guard.
5. **Reuse12:** 219 states. At the five explicit prefixes in `build218.py`,
   reassociate `((A,B),C)` into `(A,(B,C))`, reusing existing physical state 12
   for `(B,C)`. Change only `188/0 = 0 R 166` and `188/1 = 1 R 12`.
6. **Reuse150:** 219 states. At four explicit prefixes, perform the same
   reassociation, reusing existing physical state 150. Change only
   `96/0 = 0 R 98` and `96/1 = 1 R 150`.
7. **Contextual96-to85 fold:** 218 states. Redirect every target 96 to 85,
   delete the two rows of 96, and set `85/0 = 0 R 98`, `85/1 = 1 L 221`.
   The source remains identical to stage 6. The final table has exactly 218
   working states, 436 total binary rows and only the external halt target 254.

The final source has 4,744 primitive occurrences and 205 unique DAG nodes,
not 218 nodes. Source-DAG count, physical source-role count and physical
working-state count are distinct quantities. No physical-state conclusion is
drawn from the DAG count alone.

## Source theorem, without a search-history assumption

`lineage_recipe.json` contains two compact, minimal, topologically indexed
source grammars and exact old/new physical row edits. These are explicit
construction data. They do not purport to reproduce a missing random-search
history. Expanding a source grammar reconstructs all 4,744 leaf addresses and
its exact pinned source bytes.

For every stage, the checker verifies:

- a full binary, prefix-free, canonically ordered source syntax;
- the identical ordered primitive names and arguments;
- identical first 37 initialization leaf addresses;
- complete guarded ordinal control graphs by two independent resolvers;
- every integer-control target has no stray one after its resolved leaf.

The resolvers use binary successor/cut arithmetic and, separately, subtree
intervals with ancestor unwinding. There are 6,166 directed guarded successors
and 6,167 target checks including root entry. No reachable-case restriction or
finite register sample is used. `source_equivalence.py` is an unchanged copy
of the independent source worker's standalone verifier; its own main program
is not invoked by this constructor.

At corresponding source ordinal i, relate any equal natural register vectors
R. CI increments the same register; CD has the same exhaustive zero/positive
guards and either preserves or decrements the same register; CB and CC preserve
registers; CH halts. Complete ordered CFG equality supplies the same successor
ordinal for each guard. Hence all stages are strongly, step-for-step
bisimilar from every ordinal and every vector in N^9, preserving source halt
and divergence. The source theorem is independent of physical allocation.

## Physical construction and proof boundary

Every physical edit has an exact old-row precondition and a pinned result
hash. The first four stages are reconstructed from the upstream table, not
copied from an unexplained seed. Before invoking `build218.py`, the checker
requires that the reconstructed direct188 table and source are byte-identical
to that downstream constructor's basis. Thus the included basis is redundant
checked data, not an additional mathematical premise.

For all seven completed tables, the command additionally checks all 4,743
source-interior prefix blocks from dispatcher 84. Each block preserves every
prefix cell and never reads or writes any exterior cell. This yields exact
source bindings under arbitrary exterior contents. Prefix proofs do not
establish primitive arithmetic, whole blank startup, or the foundational
equiconsistency theorem.

Those obligations are discharged by separate independent audits of the final
table. In particular, a finite case pass is not an unbounded runtime proof,
and a constructor's hash match does not certify its semantics. No
proof-assistant kernel claim is made here. The constructor emits all stage
tables, sources, binding maps and `lineage.json` so the final runtime and
startup evidence can be bound to exact bytes.

## Provenance

- The explicit upstream table and source are in `upstream_basis/`.
- The source grammars and allocation row deltas are in `lineage_recipe.json`.
- The independent dual source resolvers are in `source_equivalence.py`.
- The two reuse rotations and final fold are in `build218.py`.
- The contextual fold's explicit local traces are in `contextual_fold_trace.json`.
- `build_lineage.py` composes these data and independently checks the entire
  source and physical-prefix lineage using only relative package paths.

The upstream source and physical correctness inheritance should be read with
the final independent source, startup and unbounded-runtime reports; none is
silently replaced by an intermediate-stage receipt.
