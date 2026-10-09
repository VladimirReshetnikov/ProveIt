# Source audit and attribution

## Pinned repository

The observed main revision was `8188525b70033dcfe7c51ea5ae2c8723ad0c0198`, commit message “New research reports”, dated 2026-10-09. Mathematical and adapter-specific source reads used this pin. Initial overview reads and the incoming listing preceded the pin and are used only for scope/intake context, not for an atomic-checkout execution claim.

Directly inspected maintained paths:

- `Topology/UnknotRecognition/README.md` and `reports/README.md`.
- `Topology/UnknotRecognition/synthesis/cocycle_face.tex`.
- `Topology/UnknotRecognition/synthesis/cocycle_euler.tex`.
- `Topology/UnknotRecognition/synthesis/cocycle_connectivity.tex`.
- `Topology/UnknotRecognition/fast/fastunknot/cocycle_euler.py`.
- `Topology/UnknotRecognition/fast/fastunknot/cocycle_euler_flow.py`.
- `docs/incoming/README.md` and the incoming directory listing.

Source location pattern:

`https://github.com/VladimirReshetnikov/ProveIt/blob/8188525b70033dcfe7c51ea5ae2c8723ad0c0198/<path>`

The maintained anchor-gap identity, Euler cell formula, and exact signed-flow construction are credited explicitly. `src/span_excess/network.py` adapts the sign-saturated bounded-flow construction. It is not represented as a new minimum-cost-flow method. The Hungarian span preparation is an auxiliary exact reference producer, not a claimed improvement over the maintained preparation routine.

The existing rank-one component-deletion proof is the starting point for the quantitative residual-mass theorem and the positive-secondary-cost connectedness argument. No complete literature-priority claim is made for generic additive-cost minimality.

## Incoming and prior-file scope

The latest incoming binary archives were not unpacked. In particular, the following names were visible but their contents were not audited: `unknot_minimum_envelopes_20261009.zip`, `unknot_active_faces_batched_descent_20261009.zip`, and `unknot_trace_search_20261009.zip`. They must be compared before deciding priority or overlapping integration. The recent Library representative-family articles were used only to avoid presenting their already-developed disc-completion compression direction as a new bottleneck.

## Primary external sources

Marc Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*, arXiv:2607.23350v1. The abstract/source identity and the Section 9 timing discussion were inspected; PDF page 34 was viewed. The article uses the knot-exterior boundary-compressibility criterion and the distinction between hierarchy iteration counts and a full timing specification.

`https://arxiv.org/abs/2607.23350`

Ian Agol, Joel Hass, and William P. Thurston, *The computational complexity of knot genus and spanning area*, arXiv:math/0205057v2, published in Transactions of the AMS 358 (2006), 3821–3850. The weighted-orbit theorem and Corollary 17 were inspected; PDF page 25 was viewed. This supports the use of compressed normal-component machinery rather than expansion in the represented piece count.

`https://arxiv.org/abs/math/0205057`

No third-party paper PDFs or font files are distributed. The package contains only its own article, source, and generated experiment/certificate artifacts.

## Execution boundary

No full repository checkout was executed, no maintained test total is adopted as our own, and no native knot-recognition timing or coverage result is claimed. All locally executed counts are recorded in `results/`. The native adapter is NOT_RUN. This audit is about observed source content and completed local computations, not a promise of unrecorded background validation.
