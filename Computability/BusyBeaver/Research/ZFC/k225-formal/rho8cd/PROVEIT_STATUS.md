# Status in the maintained proof checkpoint

The [phase-thirteen Lean checkpoint](../verification/k215/simplification/phase13/README.md)
uses one 58-step implication derivation for both the dominated numerical calculus
and the unrestricted named calculus. The generic core exports the unrestricted
row, composition, lifting, K, Peirce and S. Setting domination to `True` supplies
the old `Lukasiewicz` interface through a short adapter. Its entire Tarski tail
and all existing public types are preserved.

The two implication files shrink from 42,454 bytes / 811 lines to 18,243 bytes /
401 lines. The raw derivation has 58 MP steps and 23 restricted-row uses. Two
single-use goal lemmas are inlined, leaving 56 private steps; lifting adds the
existing application to a proved premise. The exact Nat adapter remains unchanged.

The [maintained producer](../generate_dominated_implication_lean.py) reads the
attributed raw Lean proof as pinned data, checks each explicit MP and relation
side condition, performs the two checked inlinings and reproduces the exact
core and numeric adapter. Its pinned ancestry input is the new six-goal derivation `4141248e…`.
The old `f0a2e60d…` ancestry input and producer31fdd remain in the preceding
checkpoint and Git history. The new producer's canonical `--check`, disposable
CLI checks and four positive / fifteen negative controls pass.

Lean checks the 179-module endpoint closure and five decoder-prefix providers,
plus three explicit API clients: 36 fresh providers and 151 exact phase-twelve
reuses. Both endpoint clients retain their ten exact axiom profiles. A separate
70-provider compatibility check preserves the old model interfaces. All nine
site batches retain their exact phase-nine records. These are external Lean
theorems; the machine and internal PA endpoint do not change.

The shared core and direct adapter are attributed to `3a7a61ee97` and
`49e99c5b7c`. Exact upstream versions, the raw 58-step proof and the overlapping
semantic import cut are preserved in the [phase-twelve merge record](../verification/k215/simplification/phase12/upstream-merge/README.md).
The earlier `88c8114d21` unrestricted proof remains a separate historical
alternative; it is superseded by the shared proof here.

The research renderer and search files are preserved as source data. Neither
was executed for this adoption. Existing Rocq sources, regeneration records,
manifest and `regenerate215.py` retain their earlier checked bytes; this work
adds no Rocq compilation or adoption. Older focused-build statements in the
research proposals remain attributed historical reports.
