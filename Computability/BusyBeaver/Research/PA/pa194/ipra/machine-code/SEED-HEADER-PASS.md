# Model-uniform first PA194 root-header pass

`PA194SeedHeaderPass.sourceHeaderPass` proves an exact physical state-24 to
state-24 run in every candidate PRA model. The source-file arguments and
header length `k` are arbitrary model elements, including nonstandard values.
No blank-suffix hypothesis is used: the eleventh source argument remains an
arbitrary encoded tape suffix, so the 25 remaining seed spares are retained.

In explanatory arithmetic, write `f = sourceFileCode(e)`, let `p` be half of
`f` after its initial zero separator, and put `s = zeros(k,2*f+1)`. The input
left half is 1 and the input right half is `256*s+1`. The output remains in
state 24 with left half 1 and right half `64*w+1`, where
`w = ones(k+1,3+8*p)`. The Lean statement records these values as nested
additions and primitive-recursive codes, and gives an exact model clock
equivalent to `2*k+40`. For the seed header length `k=40`, this is the first
120-step root-to-root pass of the concrete 462-step source instruction.

The theorem composes a model-length header scan/return with checked physical
controller rows through states 17–21, followed by a return to state 24. The
intermediate `sourceHeaderTo21`, `fourTo18`, and `returnTo24` theorems expose
the exact tape relations and accept arbitrary model-valued tails. This is one
header pass, not yet a complete source zero-branch instruction or either PA
consistency reduction.

The [two-pass continuation](TWO-HEADER-PASSES.md) composes this result with a
second root pass and retains the complete source file and arbitrary suffix.

`check-seed-header-pass.sh` rebuilds the source-frame and header modules,
checks selected direct source/object hashes, and rejects `sorryAx`. It retains
transitive prerequisite objects from the documented overlays, so this is a
suffix check rather than a full dependency-closure replay.
