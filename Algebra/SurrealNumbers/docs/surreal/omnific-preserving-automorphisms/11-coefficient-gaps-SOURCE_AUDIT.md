# Source and novelty audit

Date: 23 September 2026.

## 1. Scope of the source review

The GitHub connector was used to inspect the Surreal repository and its maintained research-report guides. The catalogue and the guides to omnific-preserving automorphisms, omnific Diophantine geometry, and surcomplex automorphisms were the main repository sources. The opening of the omnific-preserving-automorphism LaTeX manuscript was also read. These inspections are not a claim to have reviewed every proof or every report in the repository. In particular, the long Diophantine and automorphism articles were not exhaustively audited here.

The user-provided Wikipedia page was consulted for orientation. Technical background and literature comparisons instead use original research papers and standard monographs. No encyclopedic description of a known theorem is being presented as a new theorem.

Public searches addressed surreal embeddings, omnific-preserving embeddings, Hahn automorphisms, coefficient fields, and coinitiality. The checked sources did not give the central classification and its stated consequences in this form. This does not establish priority: terminology may differ, relevant work may be unindexed, and the repository contains more material than was individually inspected.

## 2. Exact repository provenance

Actual commit used for the final pin:

`cf56b89d0417cf66b26f9292654f6cae60182339`

The commits API identifies its timestamp as 2026-09-23T20:26:28Z and its Git tree as:

`21d04b0a773ab2c5aa13bd83c5932a7da5ca96bf`.

An earlier recursive-tree response returned:

`a6c68ac3826ac337762b71a2ef901997d019260c`.

That earlier value is a **tree SHA, not a commit SHA**. Initial document reads used it as a tree reference. The following stable document blobs were checked at the final actual commit, and matched the earlier reads where both were available:

| Path | Blob SHA / review scope |
|---|---|
| `docs/README.md` | `ee31a8f31f53ab167afc1dd3fc6d745e9858971a`; catalogue and maintained-guide scope |
| `docs/surreal/omnific-preserving-automorphisms/README.md` | `56a8545aa27d8ccec7cc1606d86081f932149dc6`; theorem synopsis, limitations, and questions |
| `docs/surreal/omnific-preserving-automorphisms/article.tex` | `30cdf178cb230b73a6a2de3043c98bf42aebc810`; opening through line 155, including abstract |
| `docs/surcomplex/surcomplex-field-automorphisms/README.md` | `926d6062b8fe29166893605574a49e49a82151be`; leading-term, Taylor, exponent-lift, and other theorem synopses |
| `docs/surreal/omnific-diophantine-geometry/README.md` | Read at the actual pinned commit; the returned response was truncated after substantial guide text, so no blob SHA is asserted here. The visible portion included the source table identifying the ideal test, multiplier reconstruction, and fraction-field results. |

The repository root README was also inspected earlier in the session for the general formalization infrastructure. No statement about the formal verification of the newly written theorems is inferred from that infrastructure.

## 3. Primary literature checked

- Elliot Kaplan, Lothar Sebastian Krapp, Michele Serra, *Decomposing the automorphism group of the surreal numbers*, arXiv:2509.22374v3. The inspected versioned HTML covers the automorphism decomposition, strong-sum distinction, class-size conventions, and additional omega-map questions. URL: https://arxiv.org/html/2509.22374v3
- Salma Kuhlmann, Michele Serra, *The automorphism group of a valued field of generalised formal power series*, arXiv:2107.03362v3. General lifting and automorphism background. URL: https://arxiv.org/html/2107.03362v3
- Vincent Bagayoko, Lothar Sebastian Krapp, Salma Kuhlmann, Daniel Panazzolo, Michele Serra, *Automorphisms and derivations on algebras endowed with formal infinite sums*, arXiv:2403.05827. Background attribution for formal derivation/exponential methods, not a dependence on its general correspondence for proper classes. URL: https://arxiv.org/abs/2403.05827
- David Marker, *Model Theory: An Introduction*, Springer, 2002. The publisher record was checked. The real-closed and algebraically closed quantifier-elimination results are classical background, not manuscript contributions. URL: https://doi.org/10.1007/b98860

Conway, Gonshor, and Engler--Prestel are cited as standard monographs for the classical normal-form and valued-field inputs. No new exhaustive examination of those entire books is claimed.

## 4. Old versus proposed new

| Ingredient or result | Status in this manuscript |
|---|---|
| Conway normal forms; No as the set-supported real Hahn field on No | Classical input |
| Real closedness; algebraic closedness after adjoining i; RCF/ACF quantifier elimination | Classical input |
| Exponent reindexing and coefficient Taylor automorphisms | Established construction; also present in the repository |
| Purely infinite ideal test, multiplier ring, definable coefficient field, automorphisms preserving Oz fix R, Frac(Oz)=No | Prior repository results, reproved in the needed form |
| Exact bottom-gap classification of strong exact-monomial integer-part-preserving embeddings | Proposed original contribution; priority unconfirmed |
| Coefficient motion is possible exactly at a failure of positive-image coinitiality | Consequence of that classification and the Taylor construction |
| Closedness of all classified images | Proved support-block consequence |
| Cofinality/continuity versus bounded-value/discreteness dichotomy | Proved directly, without strongness or omnific hypotheses for No |
| Explicit proper Oz-preserving embedding moving b to b+omega^-1; four combinations of the two ends | Proposed original application and synthesis |
| Continuum many copies with the same value image, field-conjugate but not conjugate by R-pointwise-fixing (hence Oz-preserving) automorphisms | Proposed original conjugacy separation |
| Parameter-fixed discrete and nondiscrete proper copies; relative coefficient-moving extension | Proposed original parameter-relative statements assembled from explicit lifts |
| Conjugation-compatible surcomplex classification and Gaussian nonelementarity | Proved transfer and reconstruction consequences |

## 5. Hypothesis audit

- The main theorem uses nonzero divisible ordered value groups and full Hahn fields with well-ordered set supports. K_0=R is used for a zero gap subgroup.
- Strongness does not include real linearity.
- Monomial preservation means coefficient-one monomials map exactly to coefficient-one monomials, not that the field embedding commutes with Conway's omega-map.
- The coefficient restriction is necessary without strongness; the classification and closed-image proof use strongness.
- Coinitiality at small positive values and cofinality at large values are distinct. All four cases are realized.
- The coefficient Taylor map alone generally does not preserve the omnific ring. Its composition with an admissible proper exponent embedding does.
- Arbitrary real-field derivations are choice-dependent and need not be continuous for the ordinary real topology.
- Class supports and all indexed sums are sets. No collection of all class automorphisms or all open subclasses is formed as an NBG object.
- The fraction-field proof is made for full No and No(i), not asserted for every set-sized Hahn field.
- The pure-field embeddings are elementary by classical quantifier elimination. The coefficient-moving expanded-pair and pure omnific-ring embeddings are explicitly proved nonelementary.
- Complex nonconjugacy is asserted for ambient automorphisms preserving both conjugation and the Gaussian omnific ring, not for all Gaussian-ring-preserving complex automorphisms.
- No omega-map or exponential automorphism conjecture is asserted to be resolved.

## 6. Verification record

The supplied Python program was run using exact rational arithmetic and passed 3,880 assertions. The report records its test categories. These are finite/truncated checks, not formal verification of the infinite or class-sized theorems.

The LaTeX source was compiled with pdfLaTeX. The resulting PDF was rendered to images; all pages were reviewed in contact sheets and representative pages in detail. Cross-references and bibliography were checked, and layout warnings were addressed. No Lean build, external referee review, or remote repository mutation was performed.
