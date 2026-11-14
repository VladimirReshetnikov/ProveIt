# Preimage selection in a Foundation universal-rule premise

`all_premise_preimage` connects the fixed binary search code from
`pa194-source-set-search-root` to the exact internal Foundation
universal-introduction premise. Given a `DerivationOf T dp` whose conclusion is
`insert (free L p) (setShift L s)`, and a member `q` of that conclusion distinct
from the distinguished `free L p`, the code returns a member of `s` whose
Foundation shift is `q`. The proof derives the required `IsFormulaSet L s`
from the premise derivation itself. The result is uniform over candidate-PRA
models with IΣ₁ arithmetic reducts, including nonstandard derivations and
formulas; `T` is a Foundation Δ₁ theory.

The distinguished-formula case is explicitly excluded and must be handled by
the surrounding compiler. This is one premise-selection lemma: no complete
nonstandard derivation traversal, full compiler correctness, PA/source-calculus
calibration, or machine halting reduction is established here.

The final module passed a fresh Lean 4.32 ordered-suffix rebuild against the
fresh binary preimage, set-search and source-shift objects and audited project
and Foundation objects. Its printed axiom dependencies are `[propext,
Classical.choice, Quot.sound]`, without `sorryAx`. The full nested replay below
is pending; the source-shift dependency has passed its own full replay.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-source-all-preimage/check.sh
```

The script rebuilds the prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.
