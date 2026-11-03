# Independent review of the direct-graph witness gap

`DirectMainGap.graph_gap` proves in every model of IΣ₁ that an actual zero of
the direct-draft output has `w<G`, provided all twelve model-valued witnesses
are strictly positive and the natural-number ports satisfy `0<beta`,
`MC<beta`, and `MF<2*beta` in the model. It does **not** assume the gap,
an old 95-graph zero, or standardness of the witnesses. The theorem proves a
model-level gap; it does not itself compose the restricted-converse theorem,
establish machine halt or produce an iPRA derivation.

The proof first derives `q≥2`, `Y≥8`, `U>0`, and `w≤X` from the stated
positivity. The checked comparison supplies a first Pell index `n≥13` and its
ordinate equation. The separate `DirectMainPellGrowth.square_bound` then
gives `Q²≤k` for `Q=X*Y²`, and `DirectMainGrowthAlgebra` gives the strict
growth bound `X+H*w<c`. A second application of `graph_indices` provides an
oriented main balance and a positive main index; the existing Pell projection
implies `(a+1)c<main`. The checked `DirectMainGapBalance.gap_of_balance`
combines these with `R+1≤k` to conclude `w<G`. The two index witnesses are
used for separate consequences of the same graph; the proof does not assert
that the two independently obtained witnesses are equal.

The first author attempt failed with an error and `sorryAx`; the second
exited zero without reported warnings or `sorryAx` and reports only
`[propext, Classical.choice, Quot.sound]` in Lean's metatheory. `check.py`
verifies the statement and critical proof applications, source/log/receipt
hashes, accepted object, Lean binary, and failed attempt. It resolves and
rehashes 18 recorded producer objects in the first-match order of the accepted
`LEAN_PATH`, checks their retained source snapshots and producer receipts, and
rehashes the 1,291 selected union objects before and after re-running earlier
comparison and conditional-gap reviews. The accepted preflight sampled one
existing Lean process and its three execution samples saw two. Sampling does
not rule out shorter overlaps or memory dips.

Run `python3 -I -S -B check.py` from this directory or provide its path from
any directory. The captured exit-zero, empty-stderr check and input hashes are
in [`observations/attempt01`](observations/attempt01/). The check requires the
retained `/tmp` provider objects; no Lean process is launched by this review.
The producer and search-path checks do not establish a full serialized-import
closure, historical source-to-object origin, package-transitive or dynamic
ancestry, or a fresh independent kernel replay. Imported first and main norm
sources locally suppress unused-variable and unused-simp-argument linters.
