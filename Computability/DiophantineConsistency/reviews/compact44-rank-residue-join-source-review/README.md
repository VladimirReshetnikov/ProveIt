# Source review: compact rank/residue join

This is an independent **source-only** review, without a Lean replay or
complete provider-closure audit. The reviewed
`compact44-rank-residue-join-prototype/CompactRankResidueJoin.lean` has
SHA-256 `82dd9d3feb27fecce93173ded53e0903208b7706223cf213567e360c97bdaf64`.
I also read the imported repository sources for the rank result, low-mask
residue, and packing-origin residue, whose respective SHA-256 values are
`3b1b93098df93925072bee932f8fbc7fb66bdee6608c7c4cfedd923d059851e8`,
`209345bfac7fad92fd4b2eb3116e095570a182a09ca9222ee2cb2fa169c5a70c`, and
`20f80330a846115b792211838fa77db3a6433ead3dca143134e5a46a7916a0a4`.
The point-in-time variation source at
`/tmp/ipra-compact44-symbolic-unit-join/src/CompactRankVariationRetry.lean`
had SHA-256 `ce394f442d6074632299ae3e6b8564f5b123eedf5625ec076b80ac1ca7e02404`;
the corresponding direct object had SHA-256
`4a83f057ab047dd1c8f16c0b716327c8a52ae2f4a2c92dac386e1a6ccc599f00`.
That observation is not independent verification of their complete ancestry.

`properties` quantifies over any `ORingStructure` model of `IΣ₁`, any
`K,N,s`, and any model-Σ₁-definable `X`. Its only explicit hypothesis is the
full `PackingInput 590069 K low high N s X` for the **symbolic compact masks**.
It concludes that the constructed rank has population
`3*(590069*N)+2`, residue 3 modulo 4, and exceeds `2*(590069*N)`.
It supplies the two former residue premises by applying the low-mask and
packing-origin theorems. The origin theorem uses `packing_low_mask`: the
repeated low-mask term is 3 modulo 4, so its no-carry partner `Cw-1` has zero
residue. No assumption about a halt, a marker, a specific kernel or a graph
zero is hidden in the source statement; the full packing remains a hypothesis.

`rank_eq_window` is stated without any packing premise and is proved by
`rfl`. Its precise parameter is
`c=(low+Exp.exp (590069*N)*(high+(Exp.exp 590069-1)))*rep 590069 N`.
This matches the reviewed `CompactRankVariation.windowRank` expression. It
does not say that a separately chosen `c` has that value; a halt-calibration
client must instantiate its arbitrary `c` accordingly and preserve the same
word, length, stride and kernel throughout.

The theorem is a model-level result. It does not itself produce a packing,
select outer or auxiliary Pell seeds, construct an exact free-J graph zero,
bind symbolic masks or kernel to retained coefficients/PDF bytes, or prove
the existence of an iPRA derivation. The author's successful build evidence
and its direct object/companion guards are separate from this source review;
no matched paired replay or complete transitive, package, or dynamic-provider
authentication is claimed here.
