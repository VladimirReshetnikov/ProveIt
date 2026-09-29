# Sources and scope of review

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `1a1396d4d3a2ac6812692df520517d86ba3a4785`.
Content was inspected through the GitHub connector. This is a version-specific
comparison, not a claim about all future repository contents.

1. `Computability/TuringDegrees/README.md`
   - Genuine oracle-recursion development and the declared assumptions of the
     separate coarse-degree library.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/1a1396d4d3a2ac6812692df520517d86ba3a4785/Computability/TuringDegrees/README.md

2. `Computability/TuringDegrees/Research/CoarseDegrees/research-plan/README.md`
   - Retired C1; C4 already has a proof sketch; C5, C6, C7, C8 are separate targets.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/1a1396d4d3a2ac6812692df520517d86ba3a4785/Computability/TuringDegrees/Research/CoarseDegrees/research-plan/README.md

3. `.../research-plan/turing_degrees_unified.tex`
   - Read the contiguous C1--C8 discussion, especially the exact C4 proposition
     and proof sketch. The article's single-ideal theorem verifies that sketch.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/1a1396d4d3a2ac6812692df520517d86ba3a4785/Computability/TuringDegrees/Research/CoarseDegrees/research-plan/turing_degrees_unified.tex

4. `.../research-synthesis/Turing_Degrees_Synthesis.tex`
   - Inspected the result inventory, core definition, spectrum identity,
     block-recovery and least-representative characterization. These are not
     claimed as newly discovered here.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/1a1396d4d3a2ac6812692df520517d86ba3a4785/Computability/TuringDegrees/Research/CoarseDegrees/research-synthesis/Turing_Degrees_Synthesis.tex

5. `.../research-reports/10/README.md`
   - Used only to identify the stated higher-computability boundary for a future
     research question. Its forcing assumptions are not theorem inputs here.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/1a1396d4d3a2ac6812692df520517d86ba3a4785/Computability/TuringDegrees/Research/CoarseDegrees/research-reports/10/README.md

## Primary mathematical sources

### Hirschfeldt--Jockusch--Kuyper--Schupp

*Coarse reducibility and algorithmic randomness*, Journal of Symbolic Logic 81
(2016), 1028--1046.

- https://arxiv.org/html/1505.01707v1
- https://arxiv.org/abs/1505.01707
- Author-hosted publication record:
  https://www.math.uchicago.edu/~drh/Papers/coarsereducibility.html

Checked Theorem 3.7 (cone-avoiding compactness), Theorem 4.2 (generic core),
and the surrounding definitions and uniformity discussion. The paper's proof
inputs are explicitly relativized with a persistent background oracle.

### Hirschfeldt--Jockusch--Schupp

*Coarse computability, the density metric, Hausdorff distances between Turing
degrees, perfect trees, and reverse mathematics*, arXiv:2106.13118v1 (2021).

- https://arxiv.org/html/2106.13118v1
- https://arxiv.org/abs/2106.13118

Checked Lemma 3.10 and Theorem 3.11(2), including its proof using a dyadic sum
of robust block codes and finite-column approximations. The theorem there has
a different stated goal; its coding architecture is already present and is
credited rather than rebranded.

### Ito--Saito--Nishizeki

*Secret sharing scheme realizing general access structure*, Electronics and
Communications in Japan (Part III: Fundamental Electronic Science) 72(9)
(1989), 56--64. DOI: 10.1002/ecjc.4430720906.

- https://onlinelibrary.wiley.com/doi/abs/10.1002/ecjc.4430720906
- https://doi.org/10.1002/ecjc.4430720906

The publisher's metadata and abstract were checked for the classical
access-structure attribution. No claim about uninspected details of its full
proof is needed: the additive construction used in the article is proved
directly, and no computability result is attributed to this source.

## Novelty assessment

The finite-profile equality with simultaneous nonattainment and the stated
relative jump control was not located in the inspected material. This does not
establish priority. Keyword searches about coarse cores, Turing ideals, and
secret sharing also returned irrelevant results; those failures are not evidence
of absence. No comprehensive review of all related degree-theoretic, mass-problem,
or infinite secret-sharing literature was completed. The article explicitly
labels the combined theorem as a proposed contribution with conventional proofs,
not an externally certified breakthrough.
