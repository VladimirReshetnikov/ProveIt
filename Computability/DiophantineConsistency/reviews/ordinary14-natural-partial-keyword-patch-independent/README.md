# Independent source review: `partial` keyword alternatives

The two [inert alternatives](../../research/ordinary14-natural-partial-keyword-patch/README.md) implement the documented 15 code-token renames and compose textually with the previously reviewed natural-81 overlay's separate predecessor edits. This is not a Lean parser run or evidence of successful elaboration.

The pinned Lean v4.32.0 parser sources declare `partial` as a declaration modifier, have `declId` begin with `ident`, and describe and implement treating a recognized keyword as a symbol. This supports the documented **likely parser hazard** for the overlay's `def partial`; the exact effective token environment and any actual parser failure remain unverified until Lean runs.

The receipt independently scans all 173 current natural-81 overlay source snapshots for the whole token `partial`, finding it only in `PartialShift82To74` and its `GraphPredecessors82` client. On their pinned text, excluding a preserved single-line doc comment, replacing that token by `partialValuation` yields the two proposed `.lean.src` files exactly: eight replacements in the first file and seven in the second. Their modules are distinct from the two predecessor-order fixes, so both changes can be applied to copies without conflict. Existing overlays and original sources remain unchanged; neither alternative is itself selected by a build.

The scan is a bounded textual observation for these pinned files, not a general Lean lexer. It does not establish that the rename is sufficient for parsing, typing, proof success, provider closure, iPRA derivability or physical-file binding.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-partial-keyword-patch-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-partial-keyword-patch-independent/result.json
```
