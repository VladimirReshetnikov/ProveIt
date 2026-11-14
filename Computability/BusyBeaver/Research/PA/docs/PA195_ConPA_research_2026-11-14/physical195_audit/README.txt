INDEPENDENT PHYSICAL AUDIT OF 195S AND 195C

Run from any directory:

  python3 verify_physical.py 195S
  python3 verify_physical.py 195C

Omitting the argument checks both sequentially. Python 3 and its standard
library suffice. Do not use Python -O: assertions are required proof checks.
The output goes to results/ and can be compared byte-for-byte with recorded/.
For automatic manifest verification and exact comparison of all four
certificate files after fresh derivation, use python3 replay.py instead.
It accepts the same optional family argument.

What is checked
---------------
Each supplied literal table has exactly 195 working controls, 390 binary
transition rows, a separate halt control, and all 195 working controls are
reachable in its directed action graph. Native initial control is 74, native
halt is 254. The dense table is independently checked to be the exact BFS
conjugate with initial 0 and halt 195.

Two independent ordinal CFG resolvers recover the same complete instruction
graph and agree with the supplied source.instructions.json. Every source
instruction is then checked on a symbolic whole-tape frame. All nine primary
registers are arbitrary natural numbers; both outcomes of every decrement
are included, without a reachability-mask restriction. The initial header
gap is 48 plus an arbitrary natural slack. The spare register list is an
arbitrary nonempty finite list of arbitrary natural values.

The engine does not call an arithmetic-box/register oracle. It follows literal
transition rows, accelerates a same-control unary sweep by its elementary
arbitrary-length induction, and uses four generic list-traversal lemmas.
Each of those four lemmas is rederived from the exact new literal table by a
symbolic one-block calculation with opaque arbitrary surrounding tape.
The empty-list and cons identities extend these calculations to arbitrary
finite lists. Every completed source contract requires exact equality of
the entire symbolic tape configuration, positive elapsed time, and the
specified head displacement. Increment may append a spare value 1, as in
the inherited compiler invariant.

Finally, the exact blank run is executed for 58,154 steps (195S) or 57,922
steps (195C). Its entire finite-support tape, head coordinate -2, and entry
control 84 must equal the source-site-25 seed with header gap 48, logical
registers [2,0,0,0,0,0,0,0,0], and 26 spare values equal to 1.

Results and scope
-----------------
195S has 3,673 source sites and 4,780 universal outcomes.
195C has 3,649 source sites and 4,749 universal outcomes.
recorded/ retains the complete per-outcome affine durations and motions,
four one-block proof traces, exact blank seeds, and summary receipts.

These are independent executable mathematical certificates for the physical
source-to-tape interface. They do not themselves prove the PA/calculus
calibration, nor constitute a new Lean/Rocq kernel theorem. The source-level
logical argument and the reassociation/folding construction are supplied in
the main report and construction artifacts.

Provenance
----------
reference/symbolic_runtime.py, independent_runtime.py, source_language.py,
and legacy_mapping.json are unmodified copies from the pinned ProveIt commit
906367250a7f96c923147b10df392294bced7be5, under
Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/allocator-screen/.
The new orchestration is verify_physical.py. PROVENANCE.json and MANIFEST.json
give exact source and artifact identities. Original license texts are retained.
