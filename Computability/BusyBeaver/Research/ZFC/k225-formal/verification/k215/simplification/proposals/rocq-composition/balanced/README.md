# Compose balanced lookup with normalized certificates

This is a new finite-data Rocq composition check and an **uncompiled Rocq glue proposal**.
It is not a new kernel-certified source theorem or a measured compilation speedup.

The separately delivered Automatic Certificates packet already uses inherited
balanced `CTree` blocks in its Lean normalized checker. Balancing plus normalization
is therefore NOT a new general idea. The present result is specifically the
combination of the inspected Rocq balanced-lookup and normalized-list checker
interfaces. The automatic Rocq lane inspected so far still uses `NCheck` over
a list; this is a bounded artifact comparison, not a global novelty claim.

The recently delivered archives separately provide a compiled ordinary balanced
lookup checker over 2,240 entries and a compiled normalized checker over 1,426
entries. The existing balanced theorem refines the exact-pointer checker, so it
cannot simply be applied to the normalized data. The latter needs `ibeq`, which
compares infinite zero-padded bit streams rather than literal lists.

`BalancedNormalized.proposal.v` keeps the already proved tree lookup/flattening
theorems and changes only the branch and entry wrappers. Its main refinement is
`nbcheck t1 t2 T = ncheck t1 t2 (flatten T)` for a valid tree. The halting theorem
then follows from the existing normalized checker's soundness theorem. No new
machine, path semantics, segment evaluator, or simulation induction is needed.
The supplied glue has not been compiled; identifier/proof-script compatibility
and the concrete instance still require proof-assistant checks.

## Independent complete finite check

`check_combined.py` parses the inert current Lean source-tree literals at commit
`aa66d0a33f1f8237a348899eb8095b045a502832` and compares their complete structure
to the previously audited tree data. It independently checks every packed Rocq
certificate entry against the normalized JSON, respecting the two different
path-code bit orders. It builds a balanced binary tree without renumbering any
entry or successor, verifies every index lookup against the original list,
and checks all normalized segment branches against the full source trees.
The finite segment fuel is 1,000, as in the inspected `Bisim230` source.

Results:

- 1,426 entries, one halt, and 2,851 checked branches including initialization.
- 32,961 balanced-tree node visits, maximum 12 for one lookup.
- The same queries would take 2,033,059 list-cons visits with linear lookup.
- All lookup results agree exactly; four malformed tree/index/entry mutations
  are rejected.
- 2,659 endpoint-side comparisons fail literal list equality while satisfying
  zero-padded equality. Retaining the normalized `ibeq` condition is essential.

The 61.68-fold reduction is in this precisely defined lookup-visit count ONLY.
It is not a ratio of kernel time, memory, proof size, or whole-build time.
Tree validity, construction and segment evaluation remain work. In particular,
the existing balanced archive reports a nontrivial construction-module cost;
emit a literal tree and benchmark the full pipeline before claiming a speedup.

## Minimal remaining integration

1. Compile the generic glue against the two pinned checker modules.
2. Emit a literal `CTree` using the supplied index tree and `Normalized215`.
3. Kernel-check its validity and exact flattening, and run `nbcheck` against the
   actual two program trees. Do not replace these equalities by hash comparisons.
4. Retain the original public source-equivalence theorem statement, update its
   generator, and rebuild affected endpoint clients with assumption reports.

The primitive Turing-machine runtime, startup and foundational calibration are
unchanged. This is intended as a smaller incremental change than introducing
a new graph semantics. The strategic arithmetic-core reductions address a
different purpose: comparing genuinely different loop implementations.

## Reproduce

Run `python check_combined.py` and `python test_combined.py` with Python 3 and
assertions enabled. Both scripts reject optimized Python. They execute no
downloaded code; all received Rocq/Lean files are inert inputs. Exact input hashes
are in `RESULT.json`. The accompanying package retains inherited notices and
licenses for the copied checker sources.
