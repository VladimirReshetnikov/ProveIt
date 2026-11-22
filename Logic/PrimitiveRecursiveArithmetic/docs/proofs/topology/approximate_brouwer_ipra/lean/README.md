# Lean companion

From this directory, run `lean Brouwer.lean` using Lean 4.19.0. The file imports
only `Std`. Three executable regression checks run during elaboration at the end of the file.

## Executable representation

For dimension `d` and mesh denominator `N > 0`, `solveWord?` searches codes
from zero through `N^d - 1`, interpreted as length-`d` words in base `N`.
For a word, `sortedTimes` orders positions by their digits, breaking ties by
decreasing position. A coordinate is incremented when its position has occurred.
`wordVertex` gives the resulting list of cumulative coordinates and `wordInput`
gives the integer barycentric coordinates. A rational sample table supplies
integer image numerators at each list. The common denominator is `N * B`, with
`B > 0`. For a finite rational table take `B` to be the product of its positive
denominators. An additional rational target may share this scale by including
its denominator and the denominator of the desired oscillation bound in the product. Positive rescaling preserves the support,
the ordering of scores, and their ties.

## Checked results

- `maxLabel_correct` proves that the first maximum on the positive support
  is a maximum over all coordinates.
- `wordInput_nonneg` and `wordInput_mass` prove simplex membership.
  `gap_mesh` proves a distance bound of one numerator unit for any pair
  of steps of a word.
- `full?_spec` extracts one concrete step of each color from the Boolean
  certificate. `solveWord_sound` and `solveWord_complete` verify the bounded
  search from the existence of a fully colored cell. `solveWord_of_odd`
  extracts the word directly from an odd count of fully colored words.
- `certified_error` proves both the uniform and the sharp error estimate
  from the full-color test, common mass, mesh, and sample oscillation.
  `solveWord_error` applies the sharp estimate directly to the output
  of the executable search, with a possibly finer-precision sample at
  the anchor. Divide integer distances by the positive `N * B` to
  obtain the rational estimate.
- `cubeLabel_correct` proves the range, lower face, upper face, and two
  sign conditions for the cubical coloring. `cube_anchor` proves the
  error bound from the opposite signs at the appropriate color witnesses.
- Three closed examples check the first returned word, its vertex sequence,
  and its labels in the two-dimensional cyclic example from the paper.

## Formalization boundary

These are ordinary Lean theorems about finite data. The simplex parity
lemma is proved in the paper. Its conclusion is the explicit existence
premise in `solveWord_complete`. To finish that proof in Lean, index
incidences by a word and a deletion slot, implement the three involution
cases and the top-face bijection, then count over the finite index range.
Use the table restricted by appending final coordinates equal to `N` for
the dimension induction. For an iPRA derivation, replace finite lists,
signed integers, and finite function arguments with the arithmetic codes
of the paper. The finite analytic and geometric comparisons become Boolean
folds over these codes.

For a shorter fixed-dimensional object-language derivation on the cube,
instantiate `LeanProofs.IPRA.Topology.SpernerCube.sperner_cube` from
the cited ProveIt revision. Quote the least-coordinate color, prove the
three hypotheses using the same bounded scan as `cubeLabel_correct`, and
extract a full Kuhn cell from the odd count by bounded search. Quote the
two signed inequalities proved by `cube_anchor` after clearing positive
denominators. The host-level Lean proofs here give the arithmetic details
for those steps. The full object-language derivation of approximate
Brouwer remains to be transcribed.

The theorem-dependency check with Lean's `#print axioms` reports only
the standard `propext` and `Quot.sound` across the named theorems.
