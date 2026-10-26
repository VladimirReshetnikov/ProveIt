# Independent review: constructed complete high mask

Verdict: **PASS**, with no finding or requested source change. I read the entire
109-line `CurrentWordHighMask2011.lean` and 48-line checks file, compared their
interfaces to the actual component proofs and packed-mask definition, and
freshly replayed both files in an isolated object overlay. This review concerns
the reverse high-mask construction from an actual marked word; it does not
claim the remaining arithmetic controller or full equation converse.

The reviewer did not author the reviewed composition or its checks. The reviewer
did author the imported padding and copy packets, as well as earlier reflected
geometry/high-digit support, and independently reviewed the constructed-word,
clause, and top-bound packets. This division of roles is explicit: the review
is independent of the composition's author, not of every transitive lemma.
The root author receipt was still being prepared when this review completed;
the conclusions here are based on the actual source and fresh replay.

## Source binding and mathematical audit

All repository paths below are relative to
`Computability/DiophantineConsistency/`.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/CurrentWordHighMask2011.lean` | `f14b90ec3d4210c75dce2e4ece4de6f50bb1b2069e26b9329309eadd1c7da74a` |
| `Lean/DiophantineConsistency/CurrentWordHighMask2011Checks.lean` | `a9d997219d9d4bf3f3d81277ac764b3fc3d61fd37062398659e98ee18cfd3ffc` |
| Direct import `CurrentWordOrigin2011.lean` | `6b6bb89e40422745154e5ef990d9909a65b740d43e86842b54fde887f5de3f56` |
| Direct import `CurrentWordPadding2011.lean` | `dcf9b865df831b0c7f4de2aa0e9060c88fd62d6fae2dd0497ea0aa2f36c6b6d7` |

The complete origin source and its checks were also read as dependency context
(checks hash `141e38f2420bb0b6aa29f3e42fdb294944a9edd7eca3dc5ae9d6d8d37108e558`).
The origin objects were reused, not freshly replayed in this review. The
literal `high_mask_word`, `maskDigits_lt`, and generic `mask_word_iff` proofs
were inspected directly.

- `cell_representation` uses the actual canonical quotient `i.val/2011` and
  remainder `i.val%2011`. The quotient is strictly below `N`, so its cast does
  not silently choose another cell. The proof includes the last cell and
  `N=1` and does not assume divisibility or coprimality of the temporal stride.
- `cell_mask_pass` exhausts every field `0..2010`: origin; padding `1..916`;
  South-copy tests `960..968`; spatial-copy tests `987..994`; marker 1004;
  clause 1005; and precisely the four zero-mask gaps. The finite-index casts
  for both copy families retain their full bounds and original orientation.
- Every branch uses the **same** `Facts`, carries, and normalized digit
  function. There is no substitution of independently chosen local solutions.
  Padding requires only Boolean control values, copy tests use the actual
  `MarkedWord` matching, and the marker is the actual shifted Start indicator
  with the established addition sign.
- The origin dependency keeps both boundary carries. It derives the origin
  digit from the previous temporal cell, then uses actual marked temporal
  matching and `Start.south = 1 ≠ 435 = Start.north` to prove global digit zero.
  Other cell origins may have digit 1, which correctly passes mask 4. No
  unique-Start premise is introduced. Zero stride and `N=1` are impossible for
  an actual `MarkedWord`, as the dependency checks explicitly demonstrate;
  the generic index and support results remain valid in those cases.
- `scalar_high_mask` uses the exact identity
  `word radix maskDigits = highPort * repunit width N - 1`. The origin
  subtraction occurs once, and both normalized digits and mask digits have
  established bounds below the actual radix. The packing equivalence therefore
  applies to the genuine digit word, not an assumed scalar mask.
- `exists_high_mask_normalization` constructs one normalization before proving
  the complete digit and scalar masks. It also derives positivity from the
  actual clause and the strict bound `F < radix^(N*2011)/radix` from the top
  field. No carry, high-mask, positive representative, clean boundary, or
  controller-success premise is supplied by the caller.

The focused checks include the final field at `N=1` and `N=2`, both ends of
every zero gap, the distinct global-origin and later-origin masks, and the
fully quantified existential scalar endpoint. No full-table numeric
enumeration is needed for this structural composition.

## Isolated fresh replay

Both sources were fully read before execution and matched the announced frozen
hashes. A temporary overlay symlinked unchanged prerequisite object bundles
and excluded the two reviewed modules. Sequential commands used the overlay
first in `LEAN_PATH`:

```sh
lean -M6000 -j1 -o /tmp/current-word-high-mask-peer-mbi2kkrs/DiophantineConsistency/CurrentWordHighMask2011.olean /home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordHighMask2011.lean
lean -M6000 -j1 -o /tmp/current-word-high-mask-peer-mbi2kkrs/DiophantineConsistency/CurrentWordHighMask2011Checks.olean /home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordHighMask2011Checks.lean
```

Both passed with no diagnostics. Main took 3.44 seconds, peak RSS 3,270,552 KiB;
checks took 3.20 seconds, peak RSS 3,258,160 KiB. All six axiom reports contain
only `propext`, `Classical.choice`, and/or `Quot.sound`. The source has no new
axiom, `sorry`, or `native_decide`. Both source hashes remained unchanged and
both independently generated objects were byte-identical to the frozen shared
objects. No shared object or source was changed by the replay.

| Artifact | SHA-256 |
| --- | --- |
| Main fresh `.olean` | `75b5ca288ad3d4b3cb64abc2935f1b0c24e99ea8e4ac50b01e373f4e289f66b8` |
| Checks fresh `.olean` | `e64582987448787aba3a8f22d705cc0762b3f81285bc7e4cb643374673bf0613` |
| Main replay log | `ccbf7baae907526b9006f6673a6b8fd0568c5750e852093d6c5ad1d6602bb68e` |
| Checks replay log | `e328cee3eaf85cc8051a6513935e130bb611a0efc387be36585294d0012c3eae` |

Commands, source/object/log hashes, and unchanged-source flags are saved in
`/tmp/current-word-high-mask-peer-mbi2kkrs/REPLAY.json`.
