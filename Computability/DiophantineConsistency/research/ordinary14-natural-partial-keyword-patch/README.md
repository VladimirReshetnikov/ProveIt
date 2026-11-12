# Inert alternatives for a `partial` identifier hazard

The unelaborated `PartialShift82To74.lean` declares a helper as `def partial`
and uses it in that module and `GraphPredecessors82.lean`. Inspection of the
pinned Lean v4.32.0 parser sources shows `partial` registered as a declaration
modifier, `declId` expecting `ident`, and a parser rule that recognizes a
registered keyword as a symbol instead of an identifier. This makes the bare
helper name a **likely parser hazard**, but no Lean parser or compiler has
been run on these files, and the actual imported parser environment has not
been verified. There may be further source or proof issues.

The two `.lean.src` files are inert proposed alternatives. They rename the
helper and its 15 code references to `partialValuation`, retaining the two
module names, theorem names and mathematical statements modulo that rename.
A one-line doc comment containing the English word “partial” is preserved.
These snapshots do not replace or modify either original `.lean` file, and
are not in the existing overlay or selected by any endpoint build. They must
be composed with the separately proposed predecessor-witness order patches,
and any resulting source snapshot, downstream imports, hash receipts and
provider plan must be independently checked before use. In particular, no
claim is made that these alternatives elaborate or establish an iPRA proof.

An [independent source review](../../reviews/ordinary14-natural-partial-keyword-patch-independent/README.md)
checks the parser evidence and both exact renames, without running Lean.

The checker pins the two original files, their two alternatives, and the
inspected toolchain parser sources. It verifies the selected parser-source
text and the complete textual delta: eight code-token replacements in the
helper module and seven in its client. It does not run Lean, parse arbitrary
Lean syntax, resolve imports, establish axiom closure or bind physical files.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural-partial-keyword-patch/check.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural-partial-keyword-patch/result.json
```
