# PA194 fixed paths and standard zipper frames

`PA194Path27Header` identifies the model arithmetic expression at the
zero-branch endpoint with the word for the fixed path to site 27. It is
uniform in every model of PRA, including model-valued `k`, file arguments
and numeric suffix; `zeroResultIsPath27` assumes the tested register is zero.
`modelWord` is a metalevel fold over a fixed finite list, interpreted in a
model. These statements do not by themselves provide a native iPRA sentence or
establish that a physical controller executes the branch.

`PA194Path27Frame.frame_bits_general` independently identifies the right-hand
numeric tape representation of the standard zipper frame for **any standard**
path, padding parameter, and finite physical register list. `frame25_bits`
and `frame27_bits` specialize it to the six- and seven-bit paths; their
respective zero-run lengths are `n+42` and `n+41`. All entries of the chosen
physical register list are included. The frame has a blank far-end tape.

`PA194Path27Frame.sourceFileSelected` ties this to the model-side source file
code over standard natural numbers. Given 11 standard arguments, `selectedFile`
contains ten entries in the `physicalArgs` order (nine registers and the spare),
and `args 10` is an arbitrary standard numeric suffix. The theorem combines
the existing standard `sourceFile` and `modelSourceFile` permutation results.
`frameSelectedBlank` composes it with the actual zipper identity when
`args 10 = 0`. It does not quantify over nonstandard model-length lists and
it does not provide a zipper for a nonzero suffix. The site-25 specialization
is thus established for standard physical frames, with the same limitation.
`PA194Path25Input.site25Input` also proves, for arbitrary model elements `k`
and `f`, that the `y6+y6+1` arithmetic input used by `twoPassesZeroTo24`
equals the site-25 `modelWord` with `zeros((k+1)+1, 1+2*f)`. Identifying its
model `k` with standard `n+40` and composing all these pieces into a single
standard-frame execution theorem remains separate.

None of these frame/numeric identities proves any source instruction executes
or establishes a literal-machine halting/consistency implication. They can be
combined with separately checked conditional execution lemmas, subject to their
stated hypotheses and the additional bridges they require.

## Replaying the final sources

`check-path27-frame.sh` rebuilds five source files sequentially into one fresh
output directory: the repository copies of `PA194ZeroOutputFile.lean` and
`PA194Path27Header.lean`, followed by the supplied `PA194Path27Frame.lean` and
`PA194SelectedFile.lean` and `PA194Path25Input.lean`. It pins all five source hashes, rejects inherited Git
internal overrides, checks the named printed axiom audits and refuses
`sorryAx`. It requires the argument `COHERENT_BASE` to be a previously
source-rebuilt, internally consistent machine-specific output with all its
M6 and PA194 dependencies, and two prebuilt general project/foundation roots.
It neither rebuilds nor validates the contents/provenance of those baseline
or general overlays; source pins do not prove object compatibility. Thus this
is a staged suffix replay, not an independent full-closure build. Produce the
coherent baseline with the repository coherent startup/header source rebuild
before relying on it; use its documented retained general foundations and a
matching Lean/Mathlib installation. Do not insert another PA194 object overlay.

The staged replay in this session used the previously source-built coherent
output `/dev/shm/pa194-header-coherent/hardlink-baseline`, whose source-rebuild
manifest SHA-256 is `24cb6eca676a5a6d74c4ac4a96b4d611b618c907f6b9a698f21a62c088640cc4`.
The manifest records the 155-module extension and preexisting startup modules;
the latter were built in the same coherent startup source replay. This path is
session-local. The two retained general foundation roots below are session-local
too, and include precompiled Lean project logic and Foundation dependencies.
Ordinary Lake/Mathlib search roots also remain precompiled.

From the repository root, using the session-local baseline and foundation paths:

```sh
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
bash "$base/check-path27-frame.sh" \
  "$PWD" \
  "$base/PA194Path27Frame.lean" \
  "$base/PA194SelectedFile.lean" \
  "$base/PA194Path25Input.lean" \
  /dev/shm/pa194-header-coherent/hardlink-baseline \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The named axiom audits have only `propext`, `Classical.choice`, and/or
`Quot.sound`; `sorryAx` is absent. This is a Lean kernel check conditional on
the imported objects and Lean's normal trusted base, not a formal proof in
PA or iPRA of the overarching consistency equivalence.
