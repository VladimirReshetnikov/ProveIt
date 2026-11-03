# Proposed compact44 occupied-cell aggregate lemma

`CompactForwardLocalCell.lean` has an **author-only single-provider compile**.
It proves a model-level calculation in any `IΣ₁` model: if the selector count
is one, its weighted complement sum is that of a specified row, and the 41
copy bits have that row's payload sum, the actual finite selector-and-copy
coefficient sum is `1 + 2^51`. Its proof combines
`CompactCoefficientDecoder.finite_decomposition`,
`Compact943Decoder.tileValue_bounds`, truncated-subtraction cancellation, and
the exponential addition law. These three sum hypotheses are explicit; the
source does not assume or claim they follow automatically from any word.

Session 38318 failed with recursion-depth exhaustion and printed `sorryAx`;
its exact source and output are retained in `observations`. Raising
`maxRecDepth` to 8192 produced session 98225, exit 0 with one linter warning.
The final source removes the warned tactic sequencing; session 71209 exited 0
with no warnings and printed `[propext, Classical.choice, Quot.sound]` for
`occupied_aggregate`, without `sorryAx`. Both preceding sources and all
three outputs are retained in `observations`. The final source SHA-256 is
`904a4e7259607f872d6ab987bc008b260a6f0be1312e9daa9f30520d5ae4832b`;
the final observed object SHA-256 is
`51fee8bacd5fe66f8f3b7311636d3a735d9f855a96b7a24f3f907e91b999f571`.

The final command used the Lean 4.32.0 binary, `-M3000 -j1
-DElab.async=false`, a 120-second timeout, root
`/tmp/compact44-forward-local-cell-explore`, and
`LEAN_PATH=/tmp/compact44-coefficient-decoder-explore/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`.
At launch the imported `CompactCoefficientDecoder.olean` SHA-256 was
`4e64948d97f2a22bb6fc3b45d80492b2410f6a0f8868d4b67feb020c65e39ff5`, matching
its earlier [single-side observation](../compact44-coefficient-decomposition-prototype/terminal-observation.json).
The 943 decoder and coefficient-mass object hashes also matched that record.
This is an author-side incremental compile over that existing exploratory
provider, not a fresh source-closure build, paired replay, or independent
audit. The imported coefficient and row decoder prototypes have their own
provider qualifications; no combined build with the word side is claimed.

The next bridge must define the 943-selector one-hot function and 41 actual
copy bits from a bounded compact row lookup, prove each of the three sum
hypotheses (including the payload's bit expansion and all seven occupancy
and anchor bits), then connect this finite local sum to the corresponding
digits of the actual packed `paramKernel rho` product. In particular, neither
the table lookup nor the symbolic kernel/retained-byte identification follows
from this lemma. Establish the mask disjointness, no-carry and neighboring
cell identities separately. This source gives no compact packed word,
positive graph zero, or iPRA derivation.
