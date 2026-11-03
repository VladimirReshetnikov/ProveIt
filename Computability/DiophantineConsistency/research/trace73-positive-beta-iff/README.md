# Positive beta removes the trace75 shift-sign premise

`Trace73PositiveBetaIff.shift_nonneg_of_positive_zero` combines the checked
trace75 transport theorem with nonnegativity of a square. In every supported
IΣ₁ model, arbitrary natural ports with positive model beta and an actual
positive trace75 zero give `0 ≤ V²B` in the model difference ring.

`positive_beta_restricted_iff` consequently shows, under the same positive
beta assumption, equivalence between:

* a positive trace75 zero satisfying **only the remaining strict center
  bound** `V²B < ι(n)`; and
* a positive literal trace73 zero satisfying `0 ≤ V²B`.

The bounds remain inside their respective existentials, for the same
valuation. In particular this is **not** an unrestricted positive-zero
equivalence, an internal halting result, an iPRA theorem, or a file-binding
theorem. It removes a genuine 75-side sign premise using K7, while leaving
both the 75-side strict center bound and the 73-side shift sign open.

The guarded author check `observations/attempt01/` and tool session 6042
exited 0 with no warning or error; both reported axiom lists are
`[propext, Classical.choice, Quot.sound]`. The object
`/tmp/trace73-positive-beta-qpr_ix0f/Trace73PositiveBetaIff.olean` has
SHA-256 `0dc4aa5fc9514cc3871a97f1080695dca0026b15cfab59b29b37597a388e69fd`.
The source SHA-256 is
`ead75cfc12a808f7400c9dfcf6fcf6bc8f10fa0f95d7aa9a6ce48d16a13b3752`;
the runner and terminal hashes are
`64912290b1edf07526bc35f10db1951dec7fccde6378eb9531dbb4e0345a9b4b` and
`0467e8161860eada085339f91a8f584ec72d8a80b3566ba8f35ef5b78ed4fee3`.

The runner selects the trace75 transport from the audited fresh 14-stage
provider and earlier trace73 transfer clients from their own provider roots.
It pins the selected direct objects and selected shared trace graph and
difference-ring objects before and after compilation. Their full combined
serialized closure, inherited historical/package/dynamic ancestry and the
external 73-row JSON correspondence have not been authenticated by this run.
No independent Lean replay or independently recorded outer receipt is claimed.

Reproduce from the repository root, with the pinned providers available and
an unused attempt identifier:

```sh
ATTEMPT=attempt02 python3 -I -S -B Computability/DiophantineConsistency/research/trace73-positive-beta-iff/run.py
```
