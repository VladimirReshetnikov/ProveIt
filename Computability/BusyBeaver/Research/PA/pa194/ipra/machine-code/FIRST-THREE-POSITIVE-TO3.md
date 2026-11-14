# First physical value three, selected positive: to dense 3

`PA194FirstThreePositiveTo3.markerFirstThreePositiveTo3` follows the first
non-first marker entry with first physical value three and selected value
`k+1`. It uses the actual nonempty following file: after the state-42 positive
branch reaches dense 1, the machine scans `k` unary cells and reaches dense 3.
The Lean theorem specifies the exact initial and final packed tape halves and
clock. The helper scan theorem is model-uniform, so the run and `k` can be
nonstandard in a candidate PRA model.

At dense 3 the right half begins with the next following register block. Its
further traversal and relationship to a source instruction or frame are not
established by this result. The theorem is conditional on the intermediate
marker layout; blank-tape reachability and either iPRA consistency implication
remain unproved.

The three new modules passed an author suffix replay against retained previously
checked overlays, reporting only `propext`, `Classical.choice`, and `Quot.sound`
and no `sorryAx`. The full nested checker `check-first-three-positive-to3.sh`
is supplied but has not been run.
