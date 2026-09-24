# Sources, scope, and proposed contribution

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Snapshot: `7af8a3026c8440944e94df89020d42ca08f4e3dd`, inspected on 23 September 2026. The branch metadata reported the commit timestamp 2026-09-23T23:01:48Z.

The targeted review inspected the root README, the report catalogue, selected report READMEs, and the matrix-shadows proof audit. In particular, the relevant records were:

- `docs/surreal/omnific-groups-and-lattices/README.md`;
- `docs/surreal/omnific-groups-and-lattices/11-matrix-shadows-PROOF_AUDIT.md`;
- the catalogue and root README's account of `docs/surreal/set-sized-quotients-of-omnific-integers/`.

Other report READMEs were inspected while selecting a direction; they are not mathematical dependencies of the article. The review was not a line-by-line audit of all repository manuscripts. No blanket assertion is made that no other repository file anticipates a particular consequence. An indexed GitHub search for “Chevalley” returned no matching result in the search used, which is a limited search result rather than a proof of absence.

## Prior results explicitly credited

The scalar universal set-sized quotient of the omnific ring, the type-A elementary-group theorem, the rank-one amalgam and countable detection theorem, the type-A Steinberg version, and several matrix-kernel and cardinal arguments are repository antecedents. The article supplies written proofs of the ingredients it needs. It does not treat an unreviewed repository assertion as a formal verification certificate.

The source audit itself is a statement of review scope, not an independent referee report.

## Proposed extensions developed here

1. A common-root-kernel ideal lemma for all finite reduced root systems with no A1 component, using only 2-divisibility of the nonunital parameter ideal.
2. Intrinsic kernel invisibility and the universal arithmetic quotient for all these elementary Chevalley types, including C2, G2, and the exceptional types.
3. A Steinberg extension and passage to other split semisimple isogeny forms for the root-generated groups.
4. A componentwise classification in the simply connected category, obtained by combining the extension with the credited rank-one obstruction.
5. A classification for current Lie rings over the omnific coefficient rings: rational perfection is exactly the condition for a universal set-sized Lie-ring quotient.
6. A general ring–group equivalence for integral unitizations and finite-cardinal-cost transfer principles.

These are proposed research contributions. No certified claim of first publication is made.

## Published sources and their roles

- Conway, *On Numbers and Games*, and Gonshor, *An Introduction to the Theory of Surreal Numbers*: classical surreal normal forms, Hahn operations, cuts, and field background.
- Meinolf Geck, *A Course on Lie algebras and Chevalley groups*, arXiv:2404.11472v3: root groups, integral constructions, and Chevalley background. https://arxiv.org/abs/2404.11472v3
- Roozbeh Hazrat, Nikolai Vavilov, and Zuhong Zhang, *Relative commutator calculus in Chevalley groups*, arXiv:1107.3009v2: integral commutator identities, including the short–short G2 identity. The relevant PDF formulas were inspected. https://arxiv.org/abs/1107.3009v2
- P. M. Cohn, *On the structure of the GL2 of a ring*, Publications Mathématiques de l'IHÉS 30 (1966), 5–53: classical rank-one matrix context. https://doi.org/10.1007/BF02684355
- Jean-Pierre Serre, *Trees*: amalgam normal forms and the standard group-theoretic background.

The article does not invoke a general relative commutator theorem after dropping its small-residue-field assumptions. In particular, Oz has an F2 quotient, and its element 2 is not a unit. The argument instead divides a free parameter inside Pi_k. It never divides the killed parameter or an element of the target group.

The user-provided Wikipedia page was used for orientation, not as a proof source. Targeted current searches were attempted, but their coverage does not establish a comprehensive novelty audit. Classical sources support the imported machinery; they do not certify the new omnific conclusions.

## Non-claims

There is no assertion that E_Phi(Oz) equals the full Chevalley group G_Phi(Oz), no computation of K2, no general classification of normal subgroups, and no global bounded commutator-width theorem. The rank-one converse is stated in the simply connected elementary category. No global exponential correspondence between abstract groups and Lie rings is assumed.

The manuscript is not independently refereed, and no new Lean proof is supplied. Finite symbolic calculations are explicitly distinguished from proofs about arbitrary supports, classes, and homomorphisms.
