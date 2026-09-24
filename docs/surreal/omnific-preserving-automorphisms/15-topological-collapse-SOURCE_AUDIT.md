# Source, proof, and novelty audit

Date: 23 September 2026.

## Exact new claim boundary

The proposed new contribution is Section 3 of the article:

- every Hahn-compatible ring topology on a dense-exponent support ring is a constant-term pullback;
- the resulting classification for the real and Gaussian omnific rings;
- the countable-monomial strengthening for the full omnific rings;
- the indiscreteness conclusion for surreal and surcomplex fields;
- the exact trivial-or-cyclic exponent-group boundary for topologizing full Hahn-field summation with jointly continuous multiplication;
- the consequent topological invisibility of omnific automorphisms.

“Hahn-compatible” means that every permitted formal Hahn sum is the topological limit of its net of finite partial sums. Ordinary ring topologies without this requirement are not excluded. Joint continuity is essential; a separately continuous pairing topology is constructed as a contrast.

These results have written proofs. They are not presented as solutions of a named historical conjecture. Neither correctness nor historical priority has been independently certified.

## A discovery during the source review

The first fetched omnific-automorphism article had file-blob SHA:

`059939b5e55f2e6a59470157b80006053987411a`

Its lines 2640–2705 explicitly stated `opa:q:strong` as open. An independent constant-term detector argument was developed in response. A later directory read found updated material, including:

- `12-automatic-strongness-SOURCE_AUDIT.md`, blob `0e4e3a10b6cc4dc50aa8a0b78a3ccb74656462a9`;
- `13-omnific-isomorphisms-SOURCE_AUDIT.md`, blob `c4d3939dd582134df06259043db833f2feced35e`;
- `11-coefficient-gaps-SOURCE_AUDIT.md`, blob `050b52ff53e7155ff99d3640f9ae87d7cc3458f5`.

The directory at that later read identified the main article blob as:

`60f3b172d4a371f0f4bf135ecec9121cce35ddc3`

These are **file-blob identifiers**, not commit identifiers. The report does not invent a commit pin or infer one from a tree or blob SHA.

Companions 12 and 13 already state automatic strongness, constant-term detection and covariance, adjoint results, the class-size failure of dual representation, and qualified surcomplex extensions. All these are credited in this manuscript. The initial novelty claim was changed, rather than leaving a stale assertion that the automorphism question remained open.

The topological classifications of Section 3 are not stated in the inspected companion audits. This is a scoped comparison, not a guarantee that no uninspected or unpublished source contains a related theorem. The updated 349 KB main article was not read in its entirety, nor was every report in the repository.

## Repository content actually consulted

Repository: https://github.com/VladimirReshetnikov/Surreal

Reads through the connected GitHub tools included the root directory and README, the documentation guide, the omnific-automorphism guide, targeted sections of its initial article, its updated directory, and the three companion audits above. The root README and the automorphism report identify the earlier omnific Diophantine reconstruction results. Their needed elementary forms are proved directly here; a full review of the large Diophantine article is not claimed.

The source scopes are distinguished from the repository's formalization status. No repository build, Lean run, or remote modification was performed. An attempted local clone failed because the container could not resolve the network hostname; the connected reader provided the source content instead.

## Public primary sources consulted

1. Salma Kuhlmann and Michele Serra, *The automorphism group of a valued field of generalised formal power series*, arXiv:2107.03362v3, revised 11 April 2022. Journal of Algebra 605 (2022), 339–376; DOI 10.1016/j.jalgebra.2022.04.023.
   https://arxiv.org/abs/2107.03362v3
   Established Hahn-automorphism and strongness framework.

2. Elliot Kaplan, Lothar Sebastian Krapp, and Michele Serra, *Decomposing the automorphism group of the surreal numbers*, arXiv:2509.22374v3, revised 23 April 2026.
   https://arxiv.org/abs/2509.22374v3
   The latest version metadata was checked. The distinction between arbitrary and strong automorphisms is relevant; no particular nonstrong example is required for the new proofs.

3. Richard Blute, Robin Cockett, Pierre-Alain Jacqmin, and Philip Scott, *Finiteness spaces and generalized power series*, arXiv:1805.09836v1, 24 May 2018.
   https://arxiv.org/html/1805.09836v1
   The support-polarity and summation-sensitive tensor framework is credited prior work. Being an internal monoid in that setting is not equated with joint continuity for the ordinary Cartesian product of topologies.

4. Vincent Bagayoko, Lothar Sebastian Krapp, Salma Kuhlmann, Daniel Panazzolo, and Michele Serra, *Automorphisms and derivations on algebras endowed with formal infinite sums*, arXiv:2403.05827v2.
   https://arxiv.org/html/2403.05827v2
   Formal summation-algebra background and a reference for further research. No unrestricted class-level operator exponential theorem is imported.

5. Darren Flynn and Khodr Shamseddine, *On the topological structure of the Hahn field and convergence of power series*, arXiv:1901.09137v1, 26 January 2019.
   https://arxiv.org/abs/1901.09137
   The abstract and relevant discussion of Hahn-field vector topologies were checked. Those topologies are not identified with the discrete-coefficient pairing topology of this article, and the new obstruction concerns every jointly continuous ring topology satisfying the full summation requirement.

Conway's and Gonshor's books are cited for classical normal-form and real-closedness background, not represented as having been newly audited cover to cover. The user-supplied Wikipedia page was orientation only.

Exact-phrase searches on Hahn summation, topological rings, constant terms, and automorphisms returned some irrelevant results. Those were not used as evidence of novelty. More specialized terminology or older literature may contain related results.

## Critical proof checks

1. Joint multiplication continuity supplies U and V with UV inside a chosen zero neighborhood. Separate continuity would not suffice.
2. A valid countable monomial sum gives a null sequence of its terms by subtracting consecutive partial sums.
3. For gamma < x < 0, both x and gamma-x are negative, and their monomial product is the fixed target monomial.
4. Reflection x -> gamma-x reverses order. The two excluded sets therefore have opposite well-order properties.
5. A densely ordered interval cannot be the union of a set with no increasing sequence and one with no decreasing sequence.
6. The closure of zero is an ideal, not just a subgroup. This is used in the field collapse and the full-surreal countable strengthening.
7. Under all-sum compatibility, a purely infinite normal form is a limit of finite sums of collapsed monomials.
8. For the countable-only full-surreal variant, a positive buffer below an entire set of positive exponents exists. This is not asserted for every set-sized group.
9. Open sets are saturated under the closure of zero. This proves the pullback classification without assuming constant-term continuity in advance.
10. In the full-field exponent theorem, a cover by a reverse well order and a well order forces the positive cone to be well ordered, hence the group to be cyclic.
11. The Laurent-series positive example handles arbitrary set-indexed families using bounded-below integer supports and coefficientwise point-finiteness.
12. Class topology language uses coded neighborhood systems; no class of arbitrary proper-class open sets is formed.
13. Scalar summability detection handles cancellation with disjoint finite incidence rows, and proves target summability before writing its sum.
14. Unrestricted Gaussian automatic strongness remains open here; valuation or conjugation compatibility is stated explicitly.

## Verification boundary

The code completed with 27,139 exact finite assertions. It does not test arbitrary topologies or establish the infinite order-covering lemmas. The article provides their written proofs. No proof-assistant certificate, independent referee report, or historical-priority certificate exists for this deliverable.
