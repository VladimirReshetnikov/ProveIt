# Source and claim audit — 8 October 2026

## Repository inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt
Area: `Topology/UnknotRecognition`.

The README and selected synthesis files were read through the connected GitHub
reader. The adaptive group and related synthesis reads used commit
`f93328fbf5b576056ad3d8110c2102a46529e514`. In particular,
`synthesis/adaptive_group.tex` establishes the explicit/compressed handoff,
independent replay, shared allowances, and the absence of a full grammar-growth
or completeness bound for its group heuristic. Its reported upstream test
counts are not represented as tests run in this package.

The `fast/fastunknot/compressed_words.py` protocol was read at commit
`8170a64c7e72b890972acf200812d6dc77ae436f`, lines 1–190 in the reader request.
The returned blob SHA was `bd68418e226813a7fa50dc87405c214970ddf50e`.
We checked the identity node, signed terminal, ordered product, inverse-building,
and earlier-child conventions used by the research exporter.

No full repository checkout, production-module import, full upstream suite,
or whole-recognizer benchmark was completed. This is a local research addition,
not an assertion that all main-branch materials have been comprehensively audited.

## External mathematics

- Meesum–Prathamesh, *Unknot Recognition Through Quantifier Elimination*,
  arXiv:1803.00413v1. HTML inspected, including the SU(2) criterion, feasibility
  bound, encoding, proof and complexity analysis.
  https://arxiv.org/html/1803.00413v1
- Renegar, *On the computational complexity and geometry of the first-order
  theory of the reals. Part I*, J. Symbolic Computation 13 (1992), 255–299.
  The bound was cross-checked as stated in Proposition 7 of Meesum–Prathamesh;
  the full 1992 article was not independently rederived or exhaustively audited.
- Kronheimer–Mrowka, *Witten's conjecture and Property P*, Geometry & Topology 8
  (2004), 295–310; arXiv:math/0311489. Used as the established nonabelian SU(2)
  representation input, also explicitly stated in Meesum–Prathamesh.
  https://arxiv.org/abs/math/0311489
- Xie–Zhang, *On meridian-traceless SU(2)-representations of link groups*,
  arXiv:2104.04839v2. The abstract states the exact irreducible meridian-traceless
  criterion, whose specialization to knots supplies the needed theorem. Its
  full gauge-theoretic proof was not independently verified in this work.
  https://arxiv.org/abs/2104.04839
- Zentner, *A class of knots with simple SU(2) representations*,
  arXiv:1501.02504; Selecta Mathematica 23 (2017), 2219–2242. Used to acknowledge
  classical binary-dihedral and SU(2)-simple context, not as a source of a new
  claim that this package first discovered that representation theory.
  https://arxiv.org/abs/1501.02504

## Current developments accounted for, not assumed

Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*,
arXiv:2607.23350v1, July 2026. The hierarchy/iteration material is not silently
promoted to a proved runtime for the new backend or the maintained recognizer.
https://arxiv.org/html/2607.23350v1

Musick, *Locally Minimal Bridge Presentations of Knots*, arXiv:2609.06492v2,
September 2026, claims polynomial-time recognition. Its abstract and claimed
algorithmic conclusions were inspected. This package does not verify or refute
that claim and does not assume it. The article's limitations are statements
about its own route, not a blanket assertion that no stronger algorithm has
been claimed.
https://arxiv.org/html/2609.06492v2

## Scope of originality and corrections

The SU(2) reduction, sum-of-squares technique, binary-dihedral setting, and Sturm
method are not claimed to be new. The contribution here is the compressed
input analysis/implementation, checkpoint tradeoff and separation, fixed-seed
optimality certificate, explicit restricted diagram bounds, and integration
contract. Priority over all existing literature has not been established.

Two unsafe *prospective* integrations are explicitly excluded: replacing true
commutators by unequal arbitrary generator images, and forcing arbitrary
transformed generators to be traceless. These are not claims that either bug
already occurs in the inspected upstream code.
