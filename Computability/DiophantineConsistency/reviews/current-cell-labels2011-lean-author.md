# Current cell labels: author implementation receipt

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
This records author inspection and checks; independent review is a separate
step. No frozen dependency or maintained equation file was edited.

Frozen source bindings:

| File under `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `CurrentCellLabels2011.lean` (311 lines) | `88698cd0d678d788c169b22915594b9ce37dd5d5c19c3d0069b190e0575f740d` |
| `CurrentCellLabels2011Checks.lean` (50 lines) | `eeb3d32db77226e9d8245876e1f80ad1603b42928e2c908416f6756b8501745c` |
| Imported `CurrentClause2011.lean` | `a76daeaa24d3b3b00cfb80e2aaa3c9082740f9f8349a8d18014c912a9001c566` |
| Imported `DoubledClause2011.lean` | `1285bb4332ad2dfabaee2a99eb1c7624d9a4c7c10e82dc3f25a2e6af92e6733f` |

The complete new sources were self-read. The copied word is defined from
all 34 actual control fields, using West978..985, North960..968,
East969..976, and South942..950 with packed shifts 0, 8, 17, and 25.
An abstract binary-sum induction proves each block's unsigned range, hence
the full word is below `2^34`. Actual tile color bounds prove the packed
tile and its complement are also unsigned 34-bit words.

`clause_convolution_word` proves the full actual clause identity

```
convolution(b+1005)
 = 2*selectorCount + 2048*(selectorPayload + copiedWord) + c(b+1),
selectorPayload = sum_i (1+packedTile(tile i))*selectorValue(i).
```

The proof splits the exact kernel `Entry` type, factors the four control
blocks, and retains the selector1 bare contribution. It does not re-enumerate
the 942 tiles or discard a collided coefficient. The physical coefficient
orientation is therefore part of the checked identity, rather than a prose
interpretation of slot names.

The generic `sum_le_one_cases` lemma works for an arbitrary finite index
type and natural-valued function. A sum at most one gives either all zero
entries or one entry equal to one with all others zero. `Selected.weighted_sum`
and `Selected.unique` then specialize any weighted sum without expanding
the concrete tile table.

The main `decode_cell` theorem takes Booleanity, actual periodic support,
the carry bound 57, the literal normalized convolution equation, the actual
high-mask tests, fractional phase `W%47=0`, a cell base, and selector count
at most one. It derives the temporal term from the actual cyclic rotation
as `c((b+1005)-(W/47))`; the whole-field offset is unrestricted. It then
proves either:

* all actual abstract selectors are zero, the copied word is zero, and
  incoming carry plus temporal bit plus bare selector1 is at most three;
* there is a unique selected actual abstract tile, its copied word is
  `2^34-1-packedTile(tile i)`, and those three low contributions total at
  most one.

The outgoing clause carry at `b+1005` is zero in both cases. Its vanishing
and the actual-digit/raw-value equality are derived from the raw bound and
normalization equation, without an incoming-zero or digit-bound premise.
No occupation premise is used. `labels_of_word` unpacks the full equality
into the four color complements, and `labels_of_zero` unpacks the empty
case. `CellDecoded.word_of_selected` makes the recovered word available at
any known selected index.

Focused checks bind all four physical block starts to the actual kernel,
restate the complete endpoint with its exact premises, and prove the forced
Start origin has South word 510 using the actual `tile 0` and physical
position-zero theorems. They also verify uniqueness of the selected index.

Fresh sequential commands, with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellLabels2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellLabels2011.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellLabels2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellLabels2011Checks.lean
```

Both exited zero. The main diagnostics are empty, SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`3e9b50181bd7385cc46e0e81ff535346a7de3611d53c45545670756f16d03b36`.
All five axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No table enumeration, `sorry`, custom axiom, or native
evaluation axiom is introduced in these sources.

Development history: the first draft needed an explicit function argument
for the finite-to-range sum conversion; the next needed an explicit change
from the named selector count to its abstract sum. An unused section-variable
warning and deprecated negation tactic spelling were also corrected. These
were elaboration issues; no mathematical premise or conclusion changed.

Scope remains conditional on one-hot selection and fractional-phase zero.
The proof does not establish those hypotheses, whole-field alignment,
occupation propagation, neighboring color matching, or the final native
refutation/consistency equivalence. The copied-word arithmetic is ready for
those subsequent bindings.
