# Source, dependency, and novelty audit

Research date: 23 September 2026.

## 1. Repository baseline

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned tree/ref used for the targeted inspection:
`934810abdde4c6d74c08777b069445de43602934`

The GitHub connector retrieved the recursive tree and the following source
material (some as explicitly line-ranged excerpts):

- `README.md`: the current project overview and its detailed description of
  algebraic, Hahn, normal-form, and actual surreal-field work.
- `docs/FORMALIZATION.md`, opening 190 lines: scope, status definitions,
  source review vs implementation, and the normal-form/real-closedness bridge.
- `docs/physics/surreal-scalars-and-spacetime/README.md`, opening 230 lines:
  the maintained physics report's detailed source and claim ledger.
- `docs/surquaternions/surquaternions/README.md`, opening 160 lines:
  the existing noncommutative algebra, strong support, spectral, implicit
  lifting, exponential, and derivative results and their limitations.

This was a targeted review of the relevant guides and coverage ledger, not
an exhaustive line-by-line review of all source manuscripts or Lean modules.
The new manuscript's proofs were developed independently of a claimed
repository build. No repository files were changed and no new Lean build
was attempted.

### Prior results that are explicitly not claimed as new

The existing physics material already covers singularity obstructions,
coefficientwise reduction of formal Einstein equations, finite quantum
standard part including a conditioning boundary, a simple inverse-time
counterexample, and global-phase/fine-topology limitations.

The existing surquaternion material already covers Hamilton algebra over
real closed fields, its 2x2 complex representation, finite spectral theory,
Hahn exp/log and BCH, the all-word-length support lemma, spectral projection
estimates, and noncommutative support-controlled implicit lifting.

The ledger at this snapshot describes actual field and normal-form bridges;
it would be inaccurate to characterize the repository as having only
abstract prerequisites. Its formal coverage nevertheless remains
clause-specific. A manuscript's presence is not proof of its formalization.

## 2. Primary literature consulted

The article contains the full bibliography. These are the principal online
sources, with their role in this work.

1. Bordemann–Waldmann, *Formal GNS Construction and States in Deformation
   Quantization*, arXiv:q-alg/9607019; CMP 195 (1998), 549–583.
   https://arxiv.org/abs/q-alg/9607019
   https://doi.org/10.1007/s002200050402
   Role: established precedent for ordered formal Laurent coefficient fields,
   positivity, and quantum state representations. Not used to assert a new
   formal GNS theorem in this article.

2. Bravyi–DiVincenzo–Loss, *Schrieffer–Wolff transformation for quantum
   many-body systems*, arXiv:1105.0675; Annals of Physics 326 (2011), 2793–2826.
   https://arxiv.org/abs/1105.0675
   https://doi.org/10.1016/j.aop.2011.06.004
   Role: classical effective-Hamiltonian and exact unitary block mechanisms.
   The article supplies its own Riccati/support proof and makes no claim to
   invent the Schrieffer–Wolff method or prove many-body locality.

3. Watrous, *The Theory of Quantum Information*, Cambridge UP, 2018.
   https://cs.uwaterloo.ca/~watrous/TQI/
   Role: ordinary instruments, trace distance, and discrimination background.
   The needed finite real-closed-field identities are proved in the article.
   The author's copyrighted manuscript is not redistributed.

4. Itoh, *On the Moduli Space of Anti-Self-Dual Yang-Mills Connections on
   Kähler Surfaces*, Publ. RIMS 19 (1983), 15–32.
   https://ems.press/content/serial-article-files/42126
   Role: primary text for the elliptic deformation complex and harmonic
   spaces. Printed pages 25–26, including Proposition 2.4 and the beginning
   of Section 3, were inspected in rendered page images. The new article
   explicitly assumes the ordinary Hodge–Green identities it needs; it does
   not derive ordinary elliptic regularity from surreal arithmetic.

5. Atiyah–Hitchin–Singer, *Self-duality in four-dimensional Riemannian
   geometry*, Proc. Royal Soc. A 362 (1978), 425–461.
   Role: classical source identified through the primary reference list of
   Itoh's paper. This audit does not claim a full fresh reading of that work.

6. Berarducci–Mantova, *Surreal numbers, derivations and transseries*,
   arXiv:1503.00315; JEMS 20 (2018), 339–390.
   https://arxiv.org/abs/1503.00315
   https://doi.org/10.4171/JEMS/769
   Role: established surreal differential/transseries structure. The
   spacetime derivatives in the new article are coefficientwise ordinary
   derivatives, not this field derivation.

7. Bournez–Guilmant, *Surreal fields stable under exponential and logarithmic
   functions*, arXiv:2201.08199.
   https://arxiv.org/abs/2201.08199
   Role: exponential-closed surreal workspaces; a generic Hahn workspace
   should not silently be assumed closed under all thermal exponentials.

8. Moretti–Oppio, *Quantum theory in quaternionic Hilbert space: How Poincaré
   symmetry reduces the theory to the standard complex one*, arXiv:1709.09246.
   https://arxiv.org/abs/1709.09246
   Role: a physically motivated reduction with explicit additional
   hypotheses, distinguished from the elementary finite whole-system
   representation proved here.

9. Nieto, *Some Mathematical and Physical Remarks on Surreal Numbers*,
   arXiv:1611.09699.
   https://arxiv.org/abs/1611.09699
   Role: a speculative physics proposal, not evidence of a successful
   singularity resolution.

Some exploratory searches returned irrelevant results. Those results were
not used. A recent quaternionic preprint surfaced during the exploratory
search but was not used as a dependency or basis for a priority claim.

## 3. Contribution and novelty ledger

| Result | What this article proves | What is not claimed |
|---|---|---|
| Finite operational reduction | Explicit finite-adaptive protocol reduction and resource scope | A new quantum-shadow principle or infinite-resource theorem |
| Rare-event leading Gram | Exact success valuation and conditional residue for nonzero branches | That the elementary Gram mechanism is new in isolation, or a free experimental amplification |
| Exact effective block | Strongly evaluated graph lift, local support monoid, all-rank uniqueness | Invention of Schrieffer–Wolff or recursive perturbation theory |
| Inverse-scale dynamics | A finite-angle low-block propagator with exact reduced probabilities | A unique global phase for unlimited imaginary arguments |
| Spectral/Gibbs hierarchy | Finite-depth algebraic splitting and finite thermal residue formula | Finite computability of arbitrary surreal notation or thermodynamic phase transitions |
| Quaternionic simulation | Exact doubled-dimensional finite instrument realization | Preservation of every tensor, locality, or composition axiom |
| Chern/action laws | Exact fixed-bundle charge and valuation of the wrong-duality action defect | New topological sectors or a new Chern–Weil mechanism |
| Hahn Kuranishi map | Strong arbitrary-rank evaluation, uniqueness, and the exact obstruction equation | Invention of Kuranishi theory or proof of ordinary elliptic regularity |
| Obstruction/action floor | Persistence of a leading quadratic obstruction, optimal valuation and leading coefficient, explicit two-scale torus instance | A classification of all instanton moduli or a blanket theorem about all higher obstructions |

The proofs are given as mathematical arguments under stated assumptions.
Whether these exact arbitrary-rank formulations or their combined
applications have appeared elsewhere is not settled by the source search.
The work should be read as a candidate research contribution requiring
independent checking and literature comparison, not an established claim
of priority or a new empirically verified theory.

## 4. Verification scope

`verification.py` executed successfully with 40 exact finite assertions.
It uses deterministic symbolic algebra, no random sample, no floating-point
tolerance, no external computational service, and no network connection.
The code includes a nonzero local transgression test rather than checking
only an identity that vanishes trivially on both sides.

The matrix graph/normalization check is truncated through degree six; the
three-level eigenvalue expansion is checked through degree eight. The toy
obstruction recursion is checked through degree eleven. These finite
checks do not prove any arbitrary-support statement. The general support,
uniqueness, and geometric arguments are in the manuscript.

The PDF was built locally with pdfLaTeX, checked for unresolved references
and box warnings, rendered page by page, and inspected in contact sheets
and selected full-page renders. Third-party papers, repository source files,
and font files are not included in this package.
