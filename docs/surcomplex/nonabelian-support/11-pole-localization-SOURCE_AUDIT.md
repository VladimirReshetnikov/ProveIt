# Source audit and novelty boundary

## Repository version

Repository: `VladimirReshetnikov/Surreal`.

Pinned **commit**: `0865f043aec113c14c69ef45006bbc7546a4e75a`.

Relevant source: `docs/surcomplex/nonabelian-support/article.tex`.

Verified blob: `c2dc2f9c3da94d4ad4479f2cacd336c0093d9b37`.

Permanent source address:
https://github.com/VladimirReshetnikov/Surreal/blob/0865f043aec113c14c69ef45006bbc7546a4e75a/docs/surcomplex/nonabelian-support/article.tex

The repository was changing during inspection. An earlier tree response had SHA `b895e8672990e8b5a56f97dd7246f9dd5f86c771`; that is not the commit used for the final provenance statement. The actual branch commit was retrieved, and the specific rank-three passage was re-read there. Its blob agrees with the previously inspected article content.

## What was inspected

The repository README, documentation inventory, selected manifest entries, and the relevant article passages were read through the GitHub connector. No claim is made to have audited every report or every Lean declaration in the repository.

Relevant article ranges included lines 1–210 (abstract and scope), 510–800 (coefficient conventions, support calculus, and ordinary inputs), and 1160–1420 (polar criterion consequences and the rank-three example). Lines 1350–1403 were re-read at the final pinned commit.

The source's important distinctions are:

1. Its Part I gives positive/integral pole-only obstructions.
2. Its Part III uses a different essential-singularity family to prove persistence after holomorphic and meromorphic Hahn localization.
3. It explicitly does not settle whether the Part I pole-only examples survive holomorphic monomial localization.
4. Its displayed rank-three example is
   `G_n = I_3 + t/(z-n) E_12 + t^(1/n) E_23`, for `n >= 2`.
5. Its polar factor is
   `P_n = I_3 + t/(z-n) E_12 - t^(1+1/n)/(z-n) E_13`.

Source labels used: `nab:eq:badG`, `nab:eq:badPH`, `nab:thm:hidden`, `nab:eq:phi`, and the localization limitation referenced as `nab:nc:localization`.

## Results developed in this continuation

- **Theorems 4.1 and 5.1:** an explicit pole-cancellation frame, valid support assembly, and Laurent triviality for every fixed-nilpotent descending-scale finite-pole family. The proof also shows integral nontriviality directly.
- **Theorem 6.1:** the additional positive gauge reduction of the exact rank-three example, followed by an explicit Laurent frame. Matrices and inverse matrices have a proved lower valuation bound of `-3/4`. That bound is not claimed optimal.
- **Theorem 7.1:** a Picard decomposition obtained by elementary factorization of the unit sheaf. This is an application of standard cohomological algebra, not a claim of a new general cohomology theorem.
- **Theorems 8.1–8.2:** persistent additive self-extension classes with free rank-two middle representatives, and an injected sequence quotient.
- **Theorem 9.1:** the explicit omnific-valued cardinal-sine family and failure of reciprocal interpolation after any ordered value-group extension.
- **Proposition 9.2:** the basic coefficientwise support criterion for ordinary discrete interpolation. This is included as a transparent standard-style consequence, not a priority claim.
- **Theorem 10.1 and Corollary 10.2:** a proper locally unit nonprincipal ideal with no common finite-halo zero, and a finite free resolution proving exact projective dimensions.
- **Theorem 10.3:** explicit non-evaluation maximal ideals and Hahn-ultrapower residue fields obtained by coefficientwise ultrafilter evaluation.
- **Theorem 11.2:** exact finite-halo zeros of the cardinal-sine family and their leading infinitesimal displacements, using the proved support-controlled recursion of Lemma 11.1.

These are written arguments and proposed contributions relative to the inspected material. Their appearance here does not establish that every consequence is new in the mathematical literature or absent from every other repository report.

## Primary literature consulted

### Hahn fields and support

Bjorn Poonen, *Maximally complete fields*, L'Enseignement Mathématique (2) 39 (1993), 87–106.

https://math.mit.edu/~poonen/papers/amsval.pdf

Used for the standard generalized-series construction and support background. The PDF's support-lemma page was inspected visually as well as in parsed text. The paper is not presented as a source of the new bundle trivialization.

### Surreal normal forms and omnific integers

Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised power series and omnific integers*, Advances in Mathematics 442 (2024), 109513; arXiv:1710.07304v5.

https://arxiv.org/html/1710.07304v5

Used for the standard normal-form description: omnific integers have no negative surreal exponents and have an integer constant coefficient. No new prime-factorization or Gonshor-conjecture claim is made.

### Ordinary complex-analytic construction

Michael Greenfield, *Constructing holomorphic functions*, Rutgers Math 503 notes, modified December 1, 2007.

https://sites.math.rutgers.edu/~greenfie/mill_courses/math503a/construction.html

Used for ordinary Weierstrass, Mittag–Leffler, and discrete entire interpolation. Each such theorem is applied to ordinary coefficient functions; a Hahn support assertion is separately justified.

### Ordinary Oka context

Franc Forstnerič and Jasna Prezelj, *Oka's principle for holomorphic fiber bundles with sprays*, Mathematische Annalen 317 (2000), 117–154.

https://users.fmf.uni-lj.si/forstneric/papers/2000Math.Ann.pdf

Used for context about ordinary holomorphic bundles on Stein bases. No Oka principle for the common-domain Hahn sheaf is assumed. The paper's first page was visually inspected.

### User-supplied overview

https://en.wikipedia.org/wiki/Surreal_number

The overview was consulted for orientation. The article relies on primary sources and explicit arguments for its mathematical conventions and claims; Wikipedia is not used to certify novelty.

## Search limitations and verification status

Targeted searches concerned Hahn holomorphic coefficient rings, vector-bundle monomial localization, Picard groups, and omnific normal forms. No matching explicit pole-localization theorem was identified. These searches are not an exhaustive search through all generalized-series, Cousin-problem, or ringed-space terminology.

No named classical conjecture is claimed solved. The specific repository question is addressed at the pinned version. Neither independent peer review nor Lean formalization was performed. No repository build, axiom audit, Wolfram verification, or automated theorem-prover check of the infinite arguments is claimed.

The bundled SymPy run passed 215 exact finite checks. The infinite support, gluing, and root-existence proofs remain written proofs, and the classical analytic inputs remain explicitly cited dependencies.
