# R(A,B) has a syntactic consistency obstruction

The modified native calculus with fourth parameter `U=R(A,B)` is consistent
by an explicit finite syntax argument. It cannot even derive `F → truth`
(the literal code 4). Therefore, assuming ZFC is consistent, this modification
cannot meet the requested ZFC-provable equivalence with Con(ZFC).

The [ordinary proof](invariant.md) constructs a class containing all literal
axioms, all identities, GEN and quantified monotonicity, then proves it closed
under MP while excluding falsum. The exact full seed/support bundle is covered;
its outer universal-quantifier shape is sufficient and its contents are not
weakened. The [checked source](DiagonalInvariant.lean) uses the actual native
Code254 constructors and proves nine exact row/bundle bindings.

[Attempt4](history/attempt4/result.json) passed under Lean 4.32.0 in 1.794 seconds,
with 12 axiom probes and zero warnings. The three invariant/nonderivability
results use only `propext`, `Classical.choice`, `Quot.sound`; the nine bindings
are axiom-free. [Verification](verification.json) checks the source/log pins.
The [scope note](checked-result.md) distinguishes this from an internal
arithmetized ZFC theorem and from a machine correctness result.

The imported Code254 pair comes from an existing accepted proof record;
its cached namespace is a declared dependency boundary, not a fresh transitive
rebuild. KCode222 had no located cached object and was not rebuilt. Its exact
G/vrel/nks/bundle definitions were source-reviewed and are preserved in
[inputs](inputs/KCode222.lean); the proved general Q-headed bundle specializes
to its complete literal seed bundle.

Both independent ordinary mathematical reviews are preserved:
[Opening](peers/opening.json) with [case analysis](peers/opening.md), and
[Reflection](peers/reflection.json) with [case analysis](peers/reflection.md).
They cover the mathematical invariant; they do not claim a Lean source or
execution review. The separate [Lean source/actual review](peers/lean-actual-review.json)
checks the final source, twelve reports and declared cache boundary without
rerunning the compiler. Opening also gives ordinary extensions to `R(B,A)`,
`R(A,C)` and `R(C,A)`. Only `R(A,B)` is formalized here. Neither result covers
`R(B,C)` or `R(C,B)`.

Adding the K combinator escapes this invariant: `T → (B → T)` and truth yield
`B → T` by MP, including the code4 excluded above. No calibration for that
larger proposal is established. The [earlier README](history/prior-README.md)
and [fresh-label analysis](history/prior-fresh-label.md) remain unchanged in
history. Their conditional semantic implications stay valid; a model-existence implication strong enough to yield Con(ZFC) cannot be
proved in ZFC from this modified calculus's consistency, if ZFC is consistent.

All four source attempts and their raw logs/results are retained under history.
Compiled objects are excluded; their hashes remain in the raw actual records.
The [original runner](run_lean.py) preserves the exact original cache invocation.
It writes fresh `/tmp` attempt directories in the original scratch layout;
reproduction on another checkout requires resolving the explicitly recorded
accepted import pair and cache paths, not rebuilding dependencies silently.
[Publication provenance](publication.json) pins every copied file.
