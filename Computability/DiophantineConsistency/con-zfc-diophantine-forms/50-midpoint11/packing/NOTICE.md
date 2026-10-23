# Attribution and scope

This package is a derived research contribution to Vladimir Reshetnikov's
ProveIt repository, prepared on 23 October 2026. The reviewed baseline is
commit `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.

The new material is the support-aware isolation criterion, the explicit
weight vector of maximum 190, its exact finite certificate, the corresponding
rebinding of the nine- and ten-variable circuits, and their new verification
receipts. The integer and natural variable reductions themselves are inherited.

The Sun10 algebra and finite circuit engine are adapted from packages 40 and
31. The Jones9 algebra and its degree-cancellation certificate are adapted from
package 45. The complete compiler tuple, finite coefficient recipe, parent
equations, and semantic reduction are inherited from package 31. The two parent
systems use transport coordinates differing by `z_old=z_new+1`; both retain
their own exact source records. No coefficient tuple is assembled from parts
of different constructions. Every original license and attribution notice
bundled here remains applicable. Selected code and data origins, exact byte hashes, and descriptions of local
changes are in `SOURCE_PINS.json`. The origins of the bundled inherited proof
notes and the meaning of their historical relative references are recorded in
`upstream/README.md`.

The new material is provided under the MIT No Attribution license (MIT-0),
as reproduced in `licenses/31-sun10/LICENSE` and in the archive-level
`LICENSE`. This is MIT-0, rather than the distinct attribution-requiring MIT
license. All inherited materials retain their original license and copyright
notices; the copies under `licenses/` and `coefficients/licenses/` govern them. The reports
under `upstream/` are source evidence, not newly independently formalized
theorems. The Wolfram/Sun or other journal/preprint articles are not bundled.

Ordinary mathematical proofs establish the new support transformation.
Finite code checks establish exact combinatorial identities, fixed coefficient
bindings, and arithmetic-circuit metrics. They do not prove the inherited
unbounded compiler theorems, do not constitute an end-to-end proof-assistant
certificate, and do not decide the consistency of ZFC.
