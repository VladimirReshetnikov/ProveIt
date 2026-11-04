# A same-tuple power gap for trace74

`Trace74PellGapBinding.lean` establishes three model-level implications in every model of `IΣ₁`:

* The two Pell ordinate identities for the **same** tuple, together with the positive offset `v 8`, imply the strict Pell ordinate gap. This uses the identity `c = k Y + v 8`; it does not need a graph-zero assumption once the two ordinate identities are given.
* For positive indices, `X ≥ 2`, and `Y ≥ 1`, the same tuple has the variable-base power gap from `Trace74NearDiagonalPellModel`; the exponent indices are shifted down by one, with the subtractions justified explicitly.
* A positive zero of the actual 74 graph at `beta ≥ 15` supplies one pair of indices with both ordinate identities, an odd main index, `n < r < 2n`, and this same-tuple power gap.

The last statement does **not** prove the additional `r ≤ n + 2` near-diagonal hypothesis, the final height estimate, the reverse guard, or an iPRA equivalence. The fixed-symbolic specialization, external display binding, and clean current-source rebuild are also not claimed here.

The author checked the source using Lean 4.32.0 with `-M3000 -j1 -DElab.async=false`, a 120-second subprocess timeout, and `--root` set to this directory. `LEAN_PATH` was `/tmp:` prepended to the captured `lean_path` field in [`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json). The output object was `/tmp/Trace74PellGapBinding.olean`. The final process exited 0 with no diagnostic output except the three `#print axioms` reports, each `[propext, Classical.choice, Quot.sound]`. Two earlier attempts failed due to addition-order elaboration in the `q ≥ 2` step; neither is a successful proof. The recorded final hashes are:

```text
Trace74PellGapBinding.lean    8d0564fe2f6bd42c7aa46efc024506b1eb5e84784a9c8c8b9374785662291ded
Trace74PellGapBinding.olean   8ffc0282fa2dc540cbba08255c19ca780234da569fd2ad2b1163418c0966445a
Trace74NearDiagonalPellModel.olean af9a5f302648ea6bab75b3bb62c8ba74e48c3922f68b0af30364b22991d621bb
```

This is an author check against temporary captured provider objects, not an independent replay. The imported object closure, search-path selection and package/dynamic ancestry were not independently authenticated in this check.
