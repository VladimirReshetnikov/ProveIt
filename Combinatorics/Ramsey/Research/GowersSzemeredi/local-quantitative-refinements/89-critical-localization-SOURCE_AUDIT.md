# Source audit and prior-work distinctions

Audit date: 7 October 2026. This records what was actually inspected; it is not
an exhaustive bibliography or a certificate of publication priority.

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

The main-reference read returned commit:

```text
8622ca7e56ddb0aef7295ad7b45937df36cca0d4
```

Inspected material included the Ramsey directory, the research tree, the
local-quantitative-refinements README and its source crosswalk, the source-43
Boolean formalization plan, and the Section 17--18 formal interfaces.

| Path under `Combinatorics/Ramsey/` | Observed blob | Relevant content |
|---|---|---|
| `Lean/GowersSzemeredi/Sections17_18.lean` | `18495f50475835ca1c497d85b0052215f865b8ca` | Corrected degree in Proposition 17.2, factorial invertibility, normalization and catalogue/theorem distinction |
| `Research/GowersSzemeredi/local-quantitative-refinements/README.md` | `1ec635141ba5b9fb2ceff2a4a1ac59107de9587b` | Merged-source crosswalk; sources 36, 43, and 46 on symmetry and Boolean phase integration |
| `Research/GowersSzemeredi/local-quantitative-refinements/43-boolean-phase-FORMALIZATION.md` | `c2c551f44ae04462f6e315aa81160ba1ee7517dd` | Boolean primitive, cubic half-rank repair and energy antecedents, formalization interfaces and limitations |

The first reads used `main`; the main reference was then recorded and both the README
and the Section 17 interface were read at that explicit commit; the latter
returned the same blob identifier as the initial read. Blob identifiers are retained so the identity
of the inspected content does not depend on later branch movement. This audit
does not claim that every research manuscript in the large merged collection was
read in full or that the formal project was built.

The source-43 formalization plan is explicit that its article treats homogeneous
multiadditive tensors, whereas the existing `IsMultilinear` predicate permits
multiaffine lower-order terms. It also makes clear that nonclassical phases need
a circle or suitable finite p-power value group. Both distinctions are preserved
in this article.

## Primary mathematical sources

### Gowers (2001)

W. T. Gowers, *A new proof of Szemeredi's theorem*, Geometric and Functional
Analysis 11 (2001), 465--588.

- DOI: https://doi.org/10.1007/s00039-001-0332-9
- Public paper inspected: https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf
- Relevant part: Section 17, especially Lemma 17.1 and Propositions 17.2 and 17.7.

The original paper's phase-removal mechanism motivates the finite-vector-space
analogue here. The corrected repository degree for Proposition 17.2 is used:
a selector with `k` variables leads to a phase of degree at most `k+1`.
Our result is not a drop-in proof of the cyclic prime-field statement under its
original hypotheses, and it is not a proof of the original progression-local
statement without boundary errors.

### Tao and Ziegler (2012)

T. Tao and T. Ziegler, *The inverse conjecture for the Gowers norm over finite
fields in low characteristic*, Annals of Combinatorics 16 (2012), 121--188.

- https://arxiv.org/abs/1101.1469

This is foundational prior work on nonclassical polynomials. The reference and
its role are also recorded in Tidor's paper. Nonclassical polynomial phases and
their coordinate forms are not inventions of the present article.

### Tidor (2022)

J. Tidor, *Quantitative bounds for the U4-inverse theorem over low characteristic
finite fields*, Discrete Analysis 2022, Paper 14, 17 pages.

- https://doi.org/10.19086/da.38591
- https://arxiv.org/html/2109.13108v2

Definition 3.1 states the repeated-variable condition for nonclassical symmetric
multilinear forms. Proposition 3.4 records necessity and Proposition 3.5 proves
surjective integration in every degree. Consequently, the critical-degree
integrability criterion in the present article is NOT claimed as a new criterion.
The article gives an elementary constructive proof of the degrees it needs.
The all-degree extension imports the established general criterion explicitly.

The paper's discussion of approximate symmetrization should not be read as a
blanket claim that every conjecture posed in 2022 remains open in 2026. The
present research questions specify the exact analytic and algebraic statements
that remain unproved in this manuscript.

### Milicevic (2026): current context only

L. Milicevic, *A quasipolynomial inverse theorem for the U^k(F_p^n) norm in the
high characteristic*, arXiv:2609.33733v1, submitted 27 September 2026, 63 pages.

- https://arxiv.org/abs/2609.33733

The abstract gives the high-characteristic condition `p >= k`. This paper is
cited only to avoid an outdated description of the broader inverse-theorem
landscape. No theorem or quantitative bound from it is used in a proof here.

## Claim-level distinctions

**Known inputs, re-proved special cases, or standard deductions:** the general
nonclassical integration criterion; the elementary symplectic decomposition and
isotropic dimension/counting facts; Gowers--Cauchy--Schwarz; Young's inequality;
the classification of uniform alternating matrices. Their use is not presented
as their discovery.

**Proposed contribution of this manuscript:** an explicit all-prime critical
normal form combined with a common-primitive, sharp quotient-moment localization
that loses no selected energy on the best coset; mixed-function localization;
the all-degree sufficient condition expressed through a pencil of mixed
Frobenius defects; and the precise separation of repair, support and energy
costs. These statements are proved in the manuscript, but publication priority
for the combined package has not been exhaustively checked.

**Computational result:** the ternary fixed-defect symbol census is finite and
exhaustive in its stated domain. It is not a global inverse theorem, an
optimization over arbitrary bounded functions, or a proof of the proposed
canonical-block extremizer conjecture.

**Still missing:** an energy-to-defect-rank estimate of the desired strength;
production of symmetry from the original selector; extension from exact cosets
to cyclic local domains; and full quantitative parameter propagation.

No source texts, prior articles, or fonts have been redistributed in this ZIP.
