# Exact extension of a twisted band

Date: 2026-10-26. ROOT read the complete187-line main,92-line checks and
author receipt, then freshly replayed both sources with
`lake env lean -M6000 -j1`. Both passed; the main log is empty and all14
axiom reports contain only standard axioms. Main output was a separate
temporary object; checks imported the frozen author object. Existing
prerequisites were reused, without a full-closure build claim.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942HelicalExtension.lean | 1ca88d926e0002f2ee0eb7974176ebbe0f400c473e3b7ab742a44421b834bdc6 |
| WangTiles942HelicalExtensionChecks.lean | 4be293fb69c978e38d562934ef42370eb34b92e7899b8b00a9d0757c3abe7cda |

The extension uses representative `(x+L)%w−L`, quotient `(x+L)/w`,
and actual band value `C representative (t+quotient)`. Positive width
puts every signed coordinate in the canonical band. Within it the
extension equals C exactly. Crossing the right endpoint returns to the
left endpoint and increases the quotient, hence time, by one. The
supplied twisted boundary equality has exactly that positive-time sign.

Allowedness and temporal matching transfer from canonical-band sites;
horizontal matching uses ordinary interior matches or the twisted
endpoint match. The derived periods are(w,−1),(0,H). Start is preserved
using the material premise0≤L<w. Width1 exercises only the twisted
endpoint case; H need not be positive until constructing a finite marked
word through the earlier quotient. Tests retain negative Euclidean
quotients, both band endpoints, the opposite-sign negative control and
the failure of origin binding when its width bound is omitted.

The focused composition constructs an actual `MarkedWord(w*H)(w:ℤ)`
with exact original canonical-band binding. No machine run, cofinality,
coprimality or unique Start is supplied or inferred. Constructing the
actual computation band remains separate work.

Check log SHA-256:
`a097dca664f283673dfcab0e5c086fb9c9663c33df3899a03465c0da6cb9662d`.
Only subsets of `propext`, `Classical.choice`, `Quot.sound` occur.
See the [author receipt](wang-tiles942-helical-extension-author.md).
The maintained decimal equation and its size metrics are unchanged.
