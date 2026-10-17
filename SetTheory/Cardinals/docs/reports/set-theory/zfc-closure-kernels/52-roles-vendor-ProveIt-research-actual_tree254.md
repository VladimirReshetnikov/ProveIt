# A reusable literal decoder tree

`ActualTree254.lean` writes out the full decoder tree of the actual
`Prog254.program` and proves `RMBisim.ptree Prog254.program = tree` by kernel
definitional equality. It has 6,459 internal nodes, 6,460 leaves and depth 34.
An independent parser checked the entire emitted tree against the actual
program rows. `generate_actual_tree254.py --check` reproduces the committed
source exactly; it reuses the untrusted reader and unfolding function from
`generate_bisim254.py`.

The explicit pinned Lean 4.32.0 compiler checked the identity in 53.53 seconds
wall time, using `LEAN_NUM_THREADS=0`; peak resident memory was 2.50 GiB. The
theorem's only axiom is `propext`. Source, generator, artifact and compiler
evidence are in `results/actual-tree254-verification.json`. This one-time
identity lets later finite checks walk literal tree constructors instead of
repeatedly evaluating the numerical program's row lookup.

The original optional upstream `generate_bisim254.py --literal-trees` output
attempted `by decide +kernel` for tree equality and failed to elaborate because
`RMBisim.Tree` has no `DecidableEq` instance. That historical rejection was
repaired with `rfl`; the default generator now shares this checked tree and
writes the other tree literally. The complete 3,010-entry symmetric
bisimulation certificate subsequently passed the pinned compiler in 555.41
seconds, with exactly the source now stored as `Bisim254.lean`. Its evidence is
in `results/bisim254-optimized-verification.json`; `--plain` still reproduces
the older numerical-lookup source. Neither successful proof uses an admitted
proof or a native evaluation oracle.

The binary site-coverage layer is separate work. This module proves neither
a binary instruction simulation nor a consistency endpoint. Jeff's verification of Mira-Cult's machine and Wade's
compiler framework remain the sources of the attributed `Prog254` program;
writing out its unfolding does not relicense that source.
