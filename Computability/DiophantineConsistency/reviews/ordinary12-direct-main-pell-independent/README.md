# Independent review of the conditional direct-main Pell lemmas

`DirectMainPell.lean` contains two checked classification lemmas for every
model `V` satisfying the recorded `IΣ₁` interface:

- `indices_of_norms` assumes `Q>0`, `k>0`, `c>0`, the first norm
  `first²=1+Q*(Q+1)*k²`, and the main norm `main²=1+delta(a)*c²`. It produces
  positive model indices `n,m`, bounded by `k,c`, and the four displayed Pell
  coordinate equations. It does not separately state positivity of `first`
  or `main`.
- `direct_indices` assumes `U,X,k,eta>0`, `Y≥8`, the explicit first norm
  for `Q=(X*Y)*Y`, and the exact direct signed-pair magnitude norm. It uses
  the earlier conditional orientation result to obtain a positive `main`
  and its direct root balance, then supplies both positive bounded Pell
  indices and coordinate equations. It likewise does not separately conclude
  `first>0`.

The reviewed source defines `delta(a)=(a+1)*(a+3)`; the checker also
independently compares coefficients for `(3+4*a)+a²=delta(a)`. This is a
source-level comparison; the selected historical Pell-library object's full
source-to-object ancestry is not established by it.

The existing `FreeJPellIndices.indices` has a different contract: it starts
from a positive-port, positive-coordinate **95-graph zero**, derives its
norms and positive roots, and concludes both the old first-root magnitude
representation and equivalence of the old `core.d` signed pair to
`U*main`. The new conditional lemmas neither derive their assumed norms from
a graph nor assert those old graph-specific representations. They generalize
the classification step, but do not automatically replace the existing
`FreeJIndices` result for downstream clients.

The recorded author run exited zero with empty stderr, no warnings and no
`sorryAx`. Both results report Lean metatheory axioms
`[propext, Classical.choice, Quot.sound]`. The source, source snapshot,
runner, binary, logs and output object match the receipt. Its selected norm
and projection imports match the exact objects from their prior accepted
runs. The checker rehashed all 1,291 selected 92-halt union objects and
symlink targets before and after, and reran the earlier read-only
projection/norm review. Two recorded samples saw at most one Lean process and
at least 18,455,552 KiB available memory; sampling is not continuous.

Run `python3 -I -S -B check.py` from this directory, or pass the script path
from another directory. Its captured run exited zero with empty stderr; see
`observations/stdout`. It requires the retained absolute `/tmp` providers and
objects. No Lean process was started during this review.

This is an independent inspection of a single author run, not a fresh
independent kernel replay. Complete historical source-to-object,
package-transitive and dynamic ancestry remain inherited. Graph-derived norm
hypotheses, index alignment, both witness directions, a 90-operation graph
equivalence and an internal iPRA proof remain separate work.
