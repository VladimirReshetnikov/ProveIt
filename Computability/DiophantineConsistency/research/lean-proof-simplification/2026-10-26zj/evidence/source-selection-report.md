# Proposal: source positivity from selection, without marking

## Exact target and result

Pinned source: `7df43cdfacb490cd3ca3acd23e39027efebf8801`,
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCarryConstruction2011.lean:97–106`.

The existing `assembled_source_pos` requires a signed stride `s` and
`WangTiles942Periodic.MarkedWord N s a`. Its proof shows that the origin digit
is one using `word_origin_of_marked`, then applies `word_pos_of_digit`.

A marked origin is stronger than what positivity needs. Every assembled cell
already contains exactly its selected tile digit. In particular,
`CurrentWordConstruction2011.word_selected a dummy marker 0` gives

```
word a dummy marker (base 0 + physicalPosition (a 0)) = 1.
```

The field notation here suppresses only the cast into `ZMod (N*2011)`.
Applying the existing `word_pos_of_digit` at that coordinate proves the
strictly stronger theorem

```
∀ a dummy marker, 0 < NativeCyclicConvolution.word radix
  (CurrentWordConstruction2011.word a dummy marker)
```

for every `N` with `[NeZero N]`. No marking, horizontal/temporal matching,
stride, or Boolean-control premise occurs in the stronger theorem.

The primary patch strengthens `assembled_source_pos` in place: delete the
`s` and `ha` arguments, retain the same conclusion, and use the existing
selected digit in cell zero. Its complete replacement proof is:

```lean
  apply word_pos_of_digit _ _
  exact (CurrentWordConstruction2011.word_selected a dummy marker 0).1.symm ▸ Nat.zero_lt_one
```

The witness index is inferred from the existing selected-coordinate equality.
The patch migrates the only maintained application in
`CurrentCarryConstruction2011Checks.lean`, deleting its trailing `s h`
arguments. That check retains its complete original statement and conclusion.
No executable definition, coefficient, witness, representation, finite tile
table, or import changes.

This is a source-level API change: external callers passing the old explicit
arguments must delete them too. A separate, mutually exclusive compatibility
patch adds `assembled_source_pos_unmarked` and retains the old marked theorem
as a wrapper. Do not apply both patches.

## Why the argument is valid

The actual packed source is the natural weighted sum

\[
 C=\sum_{i\in\mathbb Z/(2011N)}c_i\rho^{\operatorname{val}(i)},
 \qquad \rho=2^{47}.
\]

At the selected coordinate `i = base 0 + physicalPosition (a 0)`, the digit
is exactly one. The term at that index is positive because the radix is
positive, and all other terms are natural numbers. Hence `0<C`.

`physicalPosition (a 0) < 942` is already part of the existing physical
permutation API consumed by `word_selected`; the dummy slot is 977 and the
marker slot is 1004. Thus neither control can overwrite the selected
coordinate. The new proof need not repeat those disjointness inequalities:
it consumes the existing exact selected-coordinate equation.

The coordinate need not be nonzero. If the selected tile is Start, its
physical position is zero and its contribution is `rho^0 = 1`. If the tile
is another tile, its selected position is different but still inside the
selector block. Positivity does not require deciding which case holds.

## Boundary cases and retained meaning

- **N = 1:** cell zero still has a selector position below 942 in a word of
  length 2011. The proof uses that cell directly; no multi-cell argument is
  needed.
- **Arbitrary numeric dummy and marker maps:** the theorem allows all natural
  values, including values greater than one or greater than the radix.
  Such values could invalidate Boolean normalization, but cannot invalidate
  positivity. No normalization theorem is inferred from this stronger result.
- **N = 0:** excluded as before. The finite cyclic word interface requires
  `[NeZero N]` (and therefore a positive word length). No new claim is made
  for `ZMod 0`.
- **Marking and masks:** the patch removes marking only from the premise of
  source positivity. `word_origin_of_marked` remains necessary when the exact
  origin digit is the desired conclusion. Marking, matching, and Boolean
  hypotheses remain at their actual mask, tile, and carry consumers.

## Measured cost and actual consumers

The recommended signature-strengthening patch changes the source module from
108 to 105 physical lines, and leaves the check module at 52 lines. Combined,
the two files change from **160 to 157 physical lines**, **135 to 132 nonblank
lines**, and **7,886 to 7,754 UTF-8 bytes**. The proof body contracts from four
tactic lines to two, and one hypothesis line disappears. The migrated check
call deletes two explicit arguments. No helper is introduced or omitted from
these measurements.

A repository-wide search of the maintained Lean tree found exactly three
references to the name: its declaration, one application in
`CurrentCarryConstruction2011Checks.lean:44`, and one `#print axioms` command.
There are no current production callers beyond the declaration. Thus the
concrete gain today is a shorter, stronger theorem and the migrated check;
no downstream endpoint-premise savings are claimed. The transitive imports
still contain the periodic module, so no import-closure reduction is claimed.

The optional compatibility variant retains the old public signature and all
checks unchanged. It changes the source module from 108 to 118 physical lines,
94 to 103 nonblank lines, and 5,374 to 6,007 UTF-8 bytes: **+10 physical lines**.
That variant uses an intentionally explicit coordinate in a seven-line helper
body and a one-line wrapper; affected proof bodies total eight lines versus
four before. It is an API-preserving alternative, not a source compression
claim. Choose it only when external compatibility matters more than the
smaller direct strengthening.

## Novelty comparison

The complete 23-placed/five-incoming corpus was searched for the target,
unmarked source positivity, selected-coordinate positivity, and associated
source-positivity descriptions. No matching proposal was found. The nearest
prior families are one-hot support classification (L15), source/window
coherence (EX030), rank positivity (EX051), and generic scalar carry facts
(EX052). Those concern different obligations; they do not identify the
unnecessary `MarkedWord` assumption in this newly added theorem.

Do not advertise generic positivity of a sum, one-hot classification, or
packing infrastructure as new. The contribution is the exact stronger
contract of this source-construction theorem.

## Validation and artifacts

`SourceSelectionPositivity.lean` compiled successfully with Lean 4.32.0. It
checks the same finite weighted-sum positivity kernel and a source-shaped
adapter taking the exact selected-coordinate equation as its sole assembly
premise. A second adapter uses the actual conjunction shape of `Selected`
and the exact two-line replacement proof, including inference of the selected
index and the product-modulus nonzero instance. It also checks single-cell examples with arbitrary natural dummy
and marker values, both with a selected index 941 and a selected origin.
The three named checked theorems use only `propext`, `Classical.choice`, and
`Quot.sound`.

Both mutually exclusive production patches pass `git apply --check` against
the pinned source.
**The full production module and its import closure were not rebuilt.**
The standalone kernel does not import the actual project; it must not be
reported as a compiled integration patch or an axiom audit of the production
helper. The exact source adapter still requires the repository-pinned build
before adoption.

Artifacts:

- `source-selection-api-migration.patch`: recommended in-place strengthening
  and the only required maintained caller migration.
- `source_selection_api_CurrentCarryConstruction2011.lean` and
  `source_selection_api_CurrentCarryConstruction2011Checks.lean`: complete
  proposed modules for the main variant.
- `source-selection-api-metrics.json`: main variant sizes, hashes, complete
  original name-reference inventory, and compatibility warning.
- `source-selection-positivity.patch`: mutually exclusive helper and
  compatibility wrapper.
- `source_selection_CurrentCarryConstruction2011.lean`: complete proposed module.
- `SourceSelectionPositivity.lean`: compiled independent kernel and examples.
- `source-selection-validation.log` / `.json`: exact compiler results and scope.
- `source-selection-metrics.json`: complete module sizes and content hashes.
