# Independent review: ArithmeticSignedPairs

27 October 2026. **PASS; no findings or requested changes.** I read the
complete final 181-line main, 37-line Checks, scope proposal, author receipt,
author driver and independent driver before replay. The first independent
pair passes in 5.569/2.577 seconds. Both objects, both full logs and all seven
axiom reports are byte-identical to the frozen author's results. Every report
uses only `propext`, `Classical.choice`, `Quot.sound`.

The pair represents a formal difference using two arbitrary internal natural
components. Its multiplication and cross-sum equivalence do not interpret
the components in standard integers or presume an object-language quotient.
The magnitude proof covers all four relative-order orientations, including
equal components, by justified subtraction in one orientation and exact swap
identities. I checked the underlying PA-minus ordered semiring, discreteness
and modified-subtraction contracts in the imported Foundation sources.

Magnitude one for each factor is derived from the actual signed product.
The natural factor-of-one proof first rules out zero and then uses internal
discreteness and multiplication bounds. Four negative-unit exclusions give
positive unit equalities for the first, second, third and fifth factors.
Equivalence-preserving multiplication identifies their full product with
the fourth factor, deriving its positive unit equality. There is no hidden
transport premise or sign requirement on that factor. Positive scale is
used only for legitimate multiplicative cancellation in
`scaled_product5_positive`; scale zero is correctly excluded.

Checks exercise positive and negative representatives, equal components,
zero magnitude, negative one and the unexcluded fourth factor. The exact
public endpoint has a positive scale, one scaled signed-product equality
and four explicit negative-unit exclusions, returning all five additive
positive-unit equations. Binding this equality to the actual polynomial's
`splitNatural` evaluator and discharging the four literal exclusions remain
later tasks. This packet does not prove polynomial soundness, cofinal
witnesses or a final PA/HA equivalence.

I reviewed both retained author attempts. The first main's two elaboration
errors and three style notices are preserved; its Checks snapshot exists
although Checks were not executed. The final delta explicitly unfolds
cross-sum equivalence, exposes the reversed pair as a swap, and removes
no-op/style issues. The unused IΣ1 model argument is omitted only on the
definitional swap helper. No mathematical premise of the extraction endpoint
changed. Both historical source hashes were authenticated against their
own pre-command snapshots rather than the current source path.

The independent preflight rehashed the separately pinned author packet and
receipt, all 25 manifest files, all 4,699 author freeze observations, both
attempts and the unchanged prerequisite inventory. It reconstructed the
exact reachable 86-module DAG, all Foundation, and checked every current
header/source and all 344 custom artifacts. The 37 explicit package boundary
names have 111 total artifacts, comprising 37 primaries and 74 companions.
All 455 actual first providers, including implicit Init, were checked in
the new private overlay with package-only fallback. No dependency was
rebuilt; inherited cache and trace provenance qualifications are retained.

I authored the separate NegativeNorms module and reused inventory, so this
receipt does not claim independent authorship review of either. NegativeNorms
is not imported by SignedPairs. ROOT authored the new signed-pair proof;
this review and replay are independent of that implementation.

Only the two authorized leaves were compiled, with Lean 4.32,
`-M6000 -j1 -DElab.async=false`, one thread, default heartbeat bounds,
512MiB guards and fresh regular output files. Both inputs were snapshotted
before the first compiler. There was one independent attempt and no failure.
Peak RSS was 1,797,240/1,784,192 KiB. Pre/postflight made 13,706 comparisons
over 2,153 paths; the durable freeze made 3,097 further comparisons over
2,177 paths. Free space remained 667,561,984 bytes after the freeze.
Terminal evidence uses regular hardlinks to preserve immutable bytes without
duplicating inventories. No proof source, shared object, shared document or
Git state was changed.

| Module | Source SHA256 | Independently rebuilt object SHA256 |
|---|---|---|
| ArithmeticSignedPairs | 802f596f97526763820fb8bb4cd0f6619b2544eae7039577bc9f37bcb6d435a2 | 03c8f4bdf8e9e21b7ba27bacb653622b9a3a0fcc0fd90f6e71a48ec3c1c8a210 |
| ArithmeticSignedPairsChecks | 20d97e341976602819778ff4b790e559cbe01071f576d8e84fff25251d462baa | 5b2bfc5021cca80d55e6645eb8ec856d38a608b185f3388a5ff6b526d1aa83e9 |

Independent provider: `/tmp/arithmetic-signed-pairs-peer-f4gz2l0f/lib`.
The [peer packet](arithmetic-signed-pairs-peer-replay.json) is
`d78a4c6b7d3382be629a144d029e054f06c8f20461dbb4f8f31dc83c1b90450e`.
The [14-file manifest](arithmetic-signed-pairs-peer-replay/FILES.json) is
`9aa69627e17db6289cdc14f5c719ac03e43f9c98debdd404fb60cd331c7a8524`.
Executed driver SHA:
`9715700e251e6fb0c739c5ad1fc0c653ee26a7dfeb4be3d6d4418b1b8fde3204`.
Freeze driver SHA:
`07c7e5ab646ab703027dea741ccbccb864fad74754fddc88f8b610e562f6ad9d`.
The peer packet and this receipt are deliberately outside the manifest to
avoid cyclic hashes; both must be pinned separately during acceptance.
