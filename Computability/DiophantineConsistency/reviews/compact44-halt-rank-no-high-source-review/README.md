# Halt-to-rank no-high-premise client: source inspection

The inspected [`CompactHaltRankNoHigh.lean`](../../research/ordinary12-ipra-bridge/compact44-halt-rank-no-high-prototype/CompactHaltRankNoHigh.lean)
has SHA-256 `55435824670a210f41606ac05787835f0cee78c1471667c6d06d90469e0f71db`.
This is a source and point-in-time artifact inspection, **not** a fresh Lean
replay or full dependency audit. The reviewer contributed to the separately
imported all-high and origin-transfer clients, so this inspection is not
independent of those dependencies' authorship.

The theorem quantifies over any IΣ₁ model and arbitrary model elements
`T,c`. Its only displayed non-instance hypothesis is the model-internal
`first (run T) = 0`. The conclusion asserts existence of a model-Σ₁-definable
function `δ`, Boolean at all model indices, with the stated positive and
nonwrapping support; the concrete perturbed family satisfies `PackingInput`
for the symbolic kernel and masks and has the specified `windowRank`
congruence. The assertion is a model-theoretic construction, not an object
language derivation or an external halt.

The proof obtains the halt-derived marked word and its definability, chosen
power geometry and positive stride. It supplies the earlier client's base
high-mask structure from ordinary all-index high safety and the checked
origin-decrement transfer. For every selector required by the earlier
universal hypothesis, it introduces the selector's Σ₁-definability and
**global** Booleanity as local instances/hypotheses, identifies the
normalized and explicitly pulsed cell functions, obtains all-index ordinary
high safety and derives both high fields. The earlier theorem supplies the
chosen selector, packing and rank congruence. The ignored support argument in
this high-field subproof is legitimate: those particular high-field theorems
are stronger and do not require support away from zero. No missing hypothesis
or mismatch in this composition was found.

The inspected imported sources are:

* `CompactHaltRankHighFields.lean`: SHA-256
  `03cc6164b91770734ed5e210f5a41f428bf8f853f0dfe2a5396a1d7e29525ad0`;
* `CompactMarkedAllHigh.lean`: SHA-256
  `db7cd6327fe6faf7be1867f3e95a0a94f50cce85e4365c3db4e6675d488c881b`;
* `CompactHighOriginMarked.lean`: SHA-256
  `872acb5e9729cb0ccfd7bd000b7094bcbbd0a9ab32da4d54da234eaed6ca2a2e`.

The successful `attempt02` receipt records exit 0, unchanged direct and
selected overlay guards, the inspected source hash, and object SHA-256
`a98ef081d8210bacb6b25313f750d6d48f4f3a5b92335bc9ad2373eb9396dde3`.
The current `/tmp` object has that hash, and the retained log reports only
`propext`, `Classical.choice`, and `Quot.sound`. This point-in-time check
does not authenticate full source/object, package or dynamic-loading
ancestry, establish a paired replay, verify retained/displayed bytes, produce
a 12-variable graph zero, or prove existence of an iPRA derivation. See the
[client record](../../research/ordinary12-ipra-bridge/compact44-halt-rank-no-high-prototype/README.md)
for its detailed provider and execution limitations.
