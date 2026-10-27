# Independent fetch/parser-progress review

Result: PASS, with no source correction requested. I read all final main
and focused-check source, the complete imported `ArithmeticCommandWordPerm222`,
the exact `EnumPerm` state/pack/decode/fetch/execAt definitions, the complete
`ArithmeticCantor` representation, and the represented truncated-subtraction
contract in Foundation. I also read the author replay inventory and development
records and checked all21 durable author artifacts against their manifest.

The frozen source hashes are:

| Source | SHA-256 |
|---|---|
| `ArithmeticCommandFetchPerm222.lean` |`be9b925b0aa8b91cfe6bd1891d145d6b0df2cc3325d0616f6240f81a4dde1e9d`|
| `ArithmeticCommandFetchPerm222Checks.lean` |`f179c7affc76fcb4f2dd14170e9c6c06bc4e00f3f4115a2f57e53ba26e93c6a8`|
| Author replay metadata |`df9d4c47e15c3a8523245428e356c7a6d1d93a88fa28483bb6f6dc62a4efb5bc`|
| Author durable `FILES.json` |`dc237e65a0438344673f9b1aa0fc1254dbddfb1d49976273be60edab46d0ce09`|

The fixed Sigma1 graph is independent of the model: at pl=0 it pairs np
with np+1, and otherwise its represented subtraction witness is pl-1,
paired with unchanged np. Under an arbitrary ordered-ring arithmetic
structure satisfying IOpen, the graph is exactly the stated function and
has a unique output. No numerical evaluator or standard-model agreement is
used to prove this internal representation.

The continuation bound uses only the actual parser's `tail_le` and
`(pl-1)+1=pl` for pl!=0. Thus the new residual pointer is strictly below
the old nonempty shifted pointer. The pl=1 boundary retains raw0, rather
than treating it as an exhausted list; its decoded tail is0 and the
candidate counter remains np. At pl=0, the new candidate raw np has tail
at most np, with next candidate np+1. The natural adapter cases on the
actual state field and uses the proved internal continuation identity; it
does not conflate Foundation's choice-defined subtraction with `Nat.sub`
by definitional equality. It covers every state, with no cleanliness
assumption on working registers. The preserved two failed natural-adapter
drafts and subsequent check-only Cantor-zero repair match this final proof.

I independently compiled both leaves, in order, in
`/tmp/fetch222-independent-peer-jn_s8qp4`, after fully reading the new
private replay driver. Commands used the pinned Lean4.32 compiler and
`-M6000 -j1 -DElab.async=false`. Both exited0 (3.62s and1.77s), the main
log was empty, and all eight focused axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The fresh objects are
byte-identical to the author's:

- Main: `76dffa217bcd8b6d5ab5b31e35c53602010b2dcabc8e6e655ff994e84ac16b58`.
- Checks: `fc1f65405eafa356b0d679e287077132c1c99c38a8729719d93cb749a309c177`.

The overlay reused102 exact-source authenticated custom modules, including
86 Foundation modules, with360 object companions. It retained37 explicit
external package imports over nine search roots; no dependency or
Foundation rebuild was performed. The targets were absent from the cached
module list and rebuilt privately. All628 distinct source/object/evidence
pins were checked before and after each command. No shared object or
accepted source was overwritten. The full commands, inputs, logs, object
pins, driver source and checked artifact manifest are retained in
`arithmetic-command-fetchperm222-peer-replay.json`.

I did not author these two leaves or the imported parser. My earlier work
on other arithmetic/native modules and cache-authentication packets is a
dependency-review role, not independent authorship of this fetch proof.
This review establishes the scoped represented fetch and parser-progress
claims. It does not prove a complete scheduler, an internal C222 runtime
simulation, a consistency calibration, or an HA equation endpoint.
