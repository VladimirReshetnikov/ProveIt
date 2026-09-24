# Randomized area selection and manifest exclusion audit

## Original selection

Before selecting the research question, an ordered list of **120** mathematical areas was prepared and Python's `secrets.randbelow(120)` was called exactly once. The returned zero-based index was **67**, selecting the one-based item **68**, **Combinatorics on words**. There was no redraw.

The complete list, result and method are preserved in `data/selection.json`. The original executed script is preserved for audit as `notes/original_area_draw.py.txt`. It is not part of the reproduction workflow and should not be executed to replace the original result.

The SHA-256 of `"\n".join(ordered_areas).encode("utf-8")` is:

```
ea66507989230ed06b68907eef7e2e8c14f933ba70aa97b56a70fab0ea4477b6
```

This checks record integrity, not externally timestamped proof of the draw's history. The record states what was actually executed during this task.

`python3 code/area_selection.py` audits the list and selection without calling a random generator. A separate `--draw --output NEW_PATH` mode can produce a new independent record and refuses to overwrite existing files. It does not change the original selection or retrospectively justify it.

## Supplied exclusion source

Filename: `manifest(1).tex`.

SHA-256 of the actual uploaded bytes:

```
729fb6e3aef3f30c7c5284c4296681fba72b6d6af68211f178ad0bc3c5d15b41
```

The entire 1,095-line file was retrieved and read, including the final generating-functions and discrepancy entries. Its catalogue describes 71 research packages, consolidated from 80 source archives. It warns that its entries record the reports' claims and are not an independent proof audit.

## Selected problem

Natural densities, over integer lengths `n`, of the three possible values `3,4,5` of the additive complexity of the fixed point of

```
0 -> 01
1 -> 02
2 -> 0
```

The explicit source is Popoli–Shallit–Stipulanti, arXiv:2410.02409v1, Remark 19.

## Closest catalogue topics are different

The manifest's transfinite-word reports compute maximal order types for finite-alphabet words of transfinite ordinal lengths under embedding. They are not about the ordinary finite-factor additive complexity of the Tribonacci fixed point.

The manifest's binary-substitution discrepancy report concerns `0 -> 1, 1 -> (10)^m` and position-error bounds, including specific OEIS conjectures. It is a different alphabet/substitution family, a different invariant, and a different question.

The remaining catalogue entries concern ordinals and order types, surreal numbers, Hankel determinants, congruences and valuations, tetration, log-concavity, graph invariants, enumeration, and other generating-function/asymptotic targets. None of the 71 entries describes the selected Tribonacci additive-complexity proportion question.

The new article does not select a listed problem, a mere renumbering of one, or an alternative proof of a listed target. This judgment is based on the actual supplied catalogue descriptions, not on a guess from the filename.
