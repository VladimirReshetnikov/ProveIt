# AQ16 signed-binding witness transport: exploratory drafts

These sources extend the historical AQ17 author chain to the pinned
16-variable, 96-row circuit in `../aq17-positive-signed-binding/`. The
literal checker compares all 16 variable indices, four port indices, 96
operations and the output and rejects four mutations. The zero decomposition
has seven residuals.

The removed coordinate has a signed right-hand side. The Lean construction
represents that side by its natural positive and negative parts, proves the
positive part strictly dominates under positive witnesses and **beta ≥ 2**,
and reconstructs the coordinate by their truncated difference. The
dominance proof uses beta ≥ 2 to obtain q ≥ 3 and U ≥ 9; it adapts the
historical main-root orientation argument. The signed-pair transport uses
the established cancellation equality, so it does not silently replace
integer subtraction by truncated subtraction. The model theorem also proves
the actual historical beta meets the stronger bound.

Eight modules compiled successively in the same exploratory overlay,
including bidirectional transport, the shifted model equivalence and native
and standard iPRA clients. The standard endpoint uses the selected embedded
Gödel–Gentzen translation of Foundation's ZFC consistency sentence. The
selected successful `#print axioms` diagnostics showed `propext`,
`Classical.choice` and `Quot.sound`, without `sorryAx`; these are Lean
metatheory axioms, not object-theory axioms. The model compile emitted an
exponentiation-threshold warning while proving an inequality rather than
evaluating the large power.

The [observations](exploratory/observations.json) pin the graph, source and
object hashes, report the actual process exits and preserve seven failed
attempts. Failed `sorryAx` diagnostic output reflects Lean's error recovery,
not a successful theorem. The saved transport logs include both failing
diagnostics and the final successful axiom reports.

The fresh `/tmp/aq16-develop/lib` tree contains file symlinks to the
completed single-overlay AQ17 guarded author output at
`/tmp/ipra-aq17-complete-guarded-author-20261101/lib` and regular AQ16
output files. `LEAN_PATH` includes that development overlay and the same
historical Foundation package provider. The exploratory compiles did not
guard all inputs before and after execution. They do not yet constitute a
complete-chain guarded AQ16 author replay, an independently matched peer
replay, a current-source result, or a Lean theorem interpreting the PDF. The
historical parent and manually transcribed TeX decoder/rank limitations
remain in force.

`generate.py` pins the candidate and AQ17 zero-decomposition template and
produces the literal and zero decomposition. `check_literal.py` checks the
literal spelling independently. Both require ordinary, non-optimized Python.

`build_manifest.py --source-commit a8a528414339a138adac3d409ebe492c359e8f12`
freezes the previous 44 AQ22/AQ17 additions and the eight AQ16 additions,
with exact source hashes, imports and diagnostic names. It produces the
52-module `author-additions.json`, SHA-256
`081e343d107f6ff1e73b1bfded119dd3698f363169ae24c25a07b60ddff33a0d`.
The guarded runner's source policy accepted all 52 modules. The subsequent
[single-overlay author run](../../reviews/ipra-aq16-guarded-author/README.md)
exited 0 and passed an [independent artifact audit](../../reviews/ipra-aq16-guarded-author-independent-audit/README.md).
It remains a historical author-only result; a matched peer replay is pending.
