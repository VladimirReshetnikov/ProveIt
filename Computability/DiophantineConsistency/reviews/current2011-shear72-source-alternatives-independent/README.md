# Independent review of two isolated source selections

The proposed source substitutions and both selection deltas are exact at the
byte level. Their mathematical interfaces agree with the inspected sources;
no concrete mismatch was found. This is a lexical/source review: neither
alternative, its imports, compiled providers nor any theorem was checked by
Lean here.

## Magnitude source alternative

The alternate magnitude file differs from the old file in exactly three
places: the direct import changes from `ZRows.CoprimeSquares` to
`ModelArithmetic`, the corresponding ZRows namespace is removed from `open`,
and `abs_eq_ι z` is replaced by `nonneg_iff.mp (abs_nonneg z)`. Every other
byte and theorem statement/body is unchanged. In the pinned old source,
`abs_eq_ι (A : DiffRing V)` has exactly that latter expression as its body
and returns the needed orientation `|A|=ι a`.

The pinned `ModelArithmetic` source directly imports `ModelDifferenceRing`,
which declares `nonneg_iff`, as well as the discrete-order and arithmetic
negative-norm modules. The latter supply the model-language context, and the
discrete-order source imports the ring/linear-arithmetic tactics used by the
magnitude source. This makes the replacement plausible from direct source
inspection; elaboration, typeclass resolution, simplifier behavior and actual
provider selection remain untested. The alternative selection removes only
the *direct* `CoprimeSquares` frontier entry and adds `ModelArithmetic`;
it does not prove that ZRows disappears transitively.

## Private extraction source alternative

The retained private extraction source differs from the selected workspace
source in exactly one `simp only` list: it deletes the two arguments
`zero_mul` and `one_mul`. All remaining bytes, including import headers and
theorem statements and bodies outside this tactic list, are identical. The
successful stage-05 receipt records the same private source SHA and output
object SHA; it does not record a build of the unmodified workspace source.
This source selection changes only the Extraction frontier entry relative to
the preceding ModelArithmetic selection. It does not install an object,
resolve its transitive providers, or prove that the altered simp invocation
elaborates in a newly selected environment.

The independent checker verifies all pinned source bytes, both exact selection
changes, every selected draft import header, nonexternal direct frontier source
hashes, reachability and a separate acyclic topological traversal. The final
selection has 15 selected drafts and 11 direct frontier names. This bounded
lexical closure is not a complete import closure, freshness or collision audit,
object ancestry authentication, axiom report, model bridge, or iPRA endpoint.

From `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear72-magnitude-modelarithmetic-selection/check.py | cmp - research/current2011-shear72-magnitude-modelarithmetic-selection/receipt.json
    timeout 30s python3 -I -S -B research/current2011-shear72-private-extraction-source-selection/check.py | cmp - research/current2011-shear72-private-extraction-source-selection/receipt.json
    timeout 30s python3 -I -S -B reviews/current2011-shear72-source-alternatives-independent/check.py | cmp - reviews/current2011-shear72-source-alternatives-independent/receipt.json

All receipts reproduce; no Lean, build, staging or reviewed-source mutation.
