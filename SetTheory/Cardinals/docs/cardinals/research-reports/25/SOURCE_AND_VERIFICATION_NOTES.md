# Source and verification notes

## Supplied source

The research target is the definition of `Rig(lambda,q)` in the supplied second-edition synthesis. It quantifies over all nonempty families of short cofinal subsets of lambda definable from ordinals, finitely many members of V_lambda, and q as one additional parameter. It does not merely quantify over subsets of q. A member of q is not automatically an allowed parameter.

Input SHA-256 hashes:

- `Cardinals3.zip`: `0216098002316082537492ed9638fa1649482c1dd42552fc65b73f1ab1b303b6`
- `Large_Cardinals_Synthesis.tex`: `5bc7df136db93c0456c6b08e0b7ed80f0ebeb0cc6dcb2ee04fa7841f1aabcab3`
- `Large_Cardinals_Unified_Report.tex`: `0bde83812ec7569fb05340c8e75ec444cdafbd9588a23d516ba9e87d2723e5d8`

## Main hypotheses and boundaries

The calibrated assertion includes an uncountable cardinal lambda of countable cofinality and the rank bound |V_alpha| < lambda for every alpha < lambda. The bound is realized by the Prikry construction. The measurable lower bound requires only the rigidity/inner-regularity consequence, not the rank bound.

The lower bound imports Dodd–Jensen covering below an inner measurable cardinal. Its application, including the use of absolute order types rather than an assumption of inner-model cardinal correctness, is proved in the report.

The upper bound includes the Prikry-property argument, cardinal and lower-rank preservation, and the cone-isomorphism proof preserving the finite-change class name. The copying and section-saturation deductions already present in the dossier are identified as such; the new contribution there is their measurable upper bound and matching lower bound for rigidity.

The canonical Boolean algebra is complete in HOD_{ {q} }, not necessarily externally complete. Its ordinal code is in that model; its decoding map and q need not be. The extension identity is proved by coding and collapsing hereditarily definable membership structures. The no-new-bounded-subsets conclusion requires the additional hypothesis V_lambda is contained in ambient HOD.

The construction does not identify the algebra with ordinary Prikry forcing, derive a normal measure in HOD_{ {q} }, prove preservation of every higher cardinal, or exhibit HOD_{ {q} } as a ground of the entire ambient universe. It does not produce distinct hereditary models from the disjoint coded copies.

## Literature and verification

The bibliography identifies the original Dodd–Jensen and Prikry sources and modern primary-source accounts by Mitchell, Benhamou, Koepke–Räsch–Schlicht, and Goldberg. It also distinguishes the related August 2026 work of Benhamou–Cummings–Goldberg–Hayut–Poveda from the present rigid-class formulation, and the ultraexacting/I0 results of Aguilera–Bagaria–Goldberg–Lücke from the calibrated consequence.

The report's own proof audit gives the dependency of each conclusion. No Lean checking or independent proof-assistant verification is claimed. No separate font files or copies of the original source archive are distributed in this continuation package.
