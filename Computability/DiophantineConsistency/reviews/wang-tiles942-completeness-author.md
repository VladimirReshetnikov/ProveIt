# Cofinal marked-word completeness: author receipt

Date: 2026-10-26. Author: `complemented47_review`.

This is an author self-review, not an independent peer review. The
author wrote the imported CycleBand and helical geometry modules.
The complete frozen Soundness source, existing DecimalMachineZFC
source, and exact definitions of BlankHalts and ConZFC were read
before execution. No existing frozen source, shared document, or
git state was changed.

## Frozen sources

Paths are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `WangTiles942Completeness.lean` | 81 | 3626 | `fcddd37eb2cec2e11c6845226839c0ea557d9edd17175d1c60d7b4f46ec21615` |
| `WangTiles942CompletenessChecks.lean` | 60 | 2477 | `23f26e9fe078824c49936a2070a0d4a4eb38f319a1981053974cc5ccb239864c` |

The main directly imports exactly:

- `WangTiles942CycleBand`, SHA `feff6383911a22e0f496f95eff693d0ee757861831890f555cf85c5370de18e8`;
- `WangTiles942Soundness`, SHA `7380edb40832cc974606eddd2651b9b765712ac9bdb55cdb1ae1e7a83d450068`;
- `DecimalMachineZFC`, SHA `778af71680ec6aadd9858d30ace87c25012ac6b9dac02e2a483094401fc06107`.

The focused checks import only the new main module.

## Exact endpoints

`cofinal_marked_word` takes the actual halt equation
`(DecimalMachine215.machine.run T).state = none`. For every independently
chosen natural width `w ≥ 2*T+4` and height `H ≥ T+2`, with `3 ≤ H`, it
constructs an actual word indexed by `Fin 942` and proves
`MarkedWord (w*H) (w:ℤ)`. The proof chooses `L=T+2` and `R=w-L`, proves
both margin inequalities and `L+R=w`, and applies the exact finite-band
construction. It forgets the stronger band's tile-binding conclusion
only at this endpoint. No divisibility, coprimality, unique-Start, or
additional run/boundary-cleanliness condition is assumed.

`ExistsMarked` means there exist a natural `N>0`, an integer stride,
and an actual function `ZMod N → Fin 942` satisfying the existing
`MarkedWord`. The nonzero-modulus instance is carried by the positive
witness. `existsMarked_iff_blank_halts` proves

```text
ExistsMarked ↔ KDenseBridge.BlankHalts DecimalMachine215.machine.
```

For the existence direction, the theorem uses width `2*T+4` and
height `T+3`. The other direction applies the literal Soundness
theorem to the very word supplied in the existential. Soundness
uses the actual initializer, derived operating-row semantics, and
Start's north color435 versus the configuration bound433; it does
not assume an independent tiling/run equivalence.

Finally `no_marked_word_iff_conZFC` and its symmetric form compose
the existing closed decimal-machine endpoint to prove

```text
(¬ ExistsMarked) ↔ DiophantineConsistency.ConZFC.
```

This uses the unchanged syntactic definition
`ConZFC := ¬ BProv ZFCax_s [] Form.fBot`. It is an external Lean
equivalence, not a proof that ZFC is consistent, not an internal
formalization of this equivalence inside ZFC, and not a proof of
the remaining Diophantine equation converse. Those distinctions
are also stated in the new module.

## Fresh builds and checks

Complete main/check sources were read before execution; the final
main was read again before freezing. Both set `Elab.async false`
and `maxRecDepth 10000`. Sequential fresh commands were:

```sh
lake env lean -M 6000 -j 1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942Completeness.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Completeness.lean
lake env lean -M 6000 -j 1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942CompletenessChecks.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942CompletenessChecks.lean
```

Final main/check builds exited zero. The main log is empty. The first
main attempt exposed only a dependent-type simplification issue when
rewriting the modulus under its `NeZero` instance; the final proof
generalizes the right margin and substitutes the width equality
before applying the band endpoint. The statement and construction
are unchanged. Focused checks passed on their first build.

Focused checks cover the exact minimal margin split, the failure
of that allocation with one less unit of total width, the separate
three-row height guard, admissible noncoprime dimensions, independent
extra width and height, the precise existential packaging, and both
directions of the existing syntactic consistency corollary. They
assert neither an actual halt nor consistency unconditionally.

All seven axiom reports, including both ConZFC corollaries, contain
only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`,
`admit`, `native_decide`, new axiom, or incoming program execution
is used.

| Log | SHA-256 |
| --- | --- |
| `/tmp/wang-tiles942-completeness-main-stage1.log` (initial elaboration) | `c2bdc484261f3742aa6323324a531dc9ef9b613622b281317e672007a5f016fe` |
| `/tmp/wang-tiles942-completeness-main-stage2.log` (final success) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/wang-tiles942-completeness-checks-stage1.log` (final success) | `ca62ce4d174f6be1604423417763abf28a28e7a8c21130bdc5c854a94bd6d41f` |
