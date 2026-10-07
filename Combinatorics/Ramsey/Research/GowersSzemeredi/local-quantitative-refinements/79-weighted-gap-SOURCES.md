# Report 291 sources and scope

Prepared 7 October 2026. This file identifies mathematical dependencies, input versions, finite computational evidence, implementation provenance and historical-inspection limits. No claim of novelty or priority follows from this inventory.

## Public source inventory

The ten authored files are:

1. README.md
2. REPRODUCING.md
3. SOURCES.md
4. Report291.tex
5. build.py
6. companion/__init__.py
7. companion/README.md
8. companion/exact_checks.py
9. tests/test_build.py
10. tests/test_companion.py

The distribution additionally includes Report291.pdf and MANIFEST.sha256. The manifest lists the eleven other public members. The ZIP SHA-256 pin is external to the ZIP to avoid self-reference. No research file, review report, external paper or numerical optimizer is required at runtime. Their mathematical results needed here are written in the article, except for the explicitly imported Report 290 theorem below.

## The one imported classification theorem

Frozen Report 290, *The Sharp Hereditary Indicator Gap and Complete Endpoint Classification*, prepared for Vladimir Reshetnikov on 7 October 2026, proves the following for arbitrary abelian source and target groups and full-domain maps:

- The division-free nonzero-defect index-two family has weighted and indicator hereditary infima exactly 3/4
- Under (P), a(x+3h)−a(x+2h)−a(x+h)+a(x)=0 for every x,h, every map outside the affine and index-two families has indicator infimum at most 5/8

These are the relevant conclusion of Theorem 1.1, Theorem 1.2 and the index-two calculation of that report. Report 291 states this dependency precisely and does not reprint its full grid, torsion and gluing proof.

Frozen Report290.tex SHA-256:

`3bb6b49a1fe470d0b5110815f646bb503ad9cce1f95362e5ba8729a994a02b57`

This is a project mathematical source, not independent published corroboration of originality. No earlier delivered report was changed.

## Complete new mathematical inputs

The corrected weighted-gap proof and complete seven-branch certificate note were read together with two independent full mathematical reconstructions. The analytic staircase and index-three extension each received a separate independent full check. All included arguments were cleared before inclusion. The version-bound mathematical inputs are:

- Sharp weighted-gap proof: `7a4240f19b2f6f6b173a855857f771b77e47b24dc9fb491c3983655c78485a26`
- Complete seven-branch coefficient/certificate note: `d053cc1cd5e587f939ef930082d58bbb0a2ecd1882e7bed32e33179193b72818`
- Direct staircase infimum, complex quartic and nonattainment proof: `d9f1d3c1e6f1e1834614f7f47a4f5ecb51a866ffbbbcd008079989247a4dcbc8`
- Index-three exact infimum, finite-attainment and three-convolution proof: `a3682ca9318e235e3b82c854b3bda58fcafb4d42a09e10c7880f006c6b8f1056`

The domain-translation extension is a direct change of variables preserving both energies and was separately checked. The Report 291 presentation explicitly normalizes x0=0 and restores translated fiber coordinates in the convolution criterion.

An early research summary confused two across-order maxima. The corrected values used throughout Report 291 are row 6=323/491 at N=16 and row 7=143/215 at N=13. The full detailed table was already correct. Both maxima are below 17/25, so the corrected theorem and branch rejection proof are unchanged. The corrected proof hash above supersedes the earlier version.

The scalar minimizer's irreducibility is proved by Eisenstein at two for X^4+4X²−2; the irrationality consequence uses an explicit quadratic contradiction. No unproved computer minimal-polynomial claim is used.

## Exact companion

The new mathematical companion uses only Python's standard library. It independently reconstructs ordered-pair and literal ordered-quadruple counts, rather than loading a research JSON answer at runtime. It prints all seventy branch histograms and all finite target-pattern evaluations, with the finite cyclic slope retained.

Its checks include C3 and C4 polynomial coefficients, exact minimizer algebra, C9 interval histograms and the order-two spike, seven branch certificates and the direct row-three failed-mass argument, finite quotient lifts, staircase residue formulas including negative indices, H_M/J_M counts, exact finite-error polynomial algebra and completed finite index-three convolution examples. Normal and optimized runs must have identical output. Input guards and mathematical checks use runtime exceptions, not assertions removed by optimization.

The complete API bounds, test scope and exclusions are in companion/README.md. Bounded diagnostics do not prove Fourier injectivity, arbitrary-group classification, continuous real minimization or nonattainment. The arbitrary-target branch reduction is exhaustive because of the symbolic proof in the article, not because small cyclic targets were sampled.

## Guarded builder provenance

build.py and tests/test_build.py are identity-only adaptations of the frozen Report 290 public builder and test suite. The report number, path/basename labels and archive name were changed; safety and reproducibility logic was retained. The new companion and mathematical regression suite are Report 291-specific. Existing installed tools are used; no package was installed and no upstream repository was edited.

The reference versions are Linux; Python 3.12.14; zlib 1.3.2; pdfTeX 3.141592653-2.6-1.40.26, TeX Live 2025/dev/Debian. Full reproduction commands, resource limits and toolchain caveats are in REPRODUCING.md.

## Primary literature and exact distinctions

### Gowers on respected quadruples and universal weighted tests

W. T. Gowers, *A new proof of Szemerédi's theorem*, Geometric and Functional Analysis 11 (2001), 465–588.

Primary PDF: https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

Inspected Sections 6 and 14, including Lemma 6.2, the product-property definition and Lemmas 14.2–14.3. Section 6 identifies respected additive quadruples with graph energy. Section 14 already quantifies over every nonnegative weight. Its lower-bound normalization is N^(-1)(sum f)^4, whereas Report 291 studies respected energy divided by E_G(f). These expressions are not interchangeable; E_G(f) is at least that fourth-mass normalization and may be much larger. Universal all-weight testing is therefore not itself claimed as new.

### Lubinsky and fixed-degree fourth-power sampling

D. S. Lubinsky, *On sharp constants in Marcinkiewicz-Zygmund and Plancherel-Polya inequalities*, Proceedings of the American Mathematical Society 142 (2014), 3575–3584.

DOI: https://doi.org/10.1090/S0002-9939-2014-12270-2
Author PDF: https://lubinsky.math.gatech.edu/Research%20papers/MarZygPlaPolMay2013PAMS.pdf

Inspected the introduction, inequality (1.2), main theorem statements and concluding strict-inequality discussion. The framework compares continuous L^p polynomial norms with values at roots of unity and asks for constants uniform in degree. Report 291's complex quartic is exactly the fixed n=3,p=4 case for degree at most two. The Parseval/modulo-three identification is derived explicitly in the article. No explicit sharp fixed n=3 value was located in the inspected passages; this does not settle its publication priority or the uniform-in-degree problem.

### Diaconis Shao and Soundararajan on carries

P. Diaconis, X. Shao and K. Soundararajan, *Carries, group theory, and additive combinatorics*, American Mathematical Monthly 121 (2014), 674–688.

Record: https://arxiv.org/abs/1309.0434
Primary preprint: https://arxiv.org/pdf/1309.0434

Inspected the introduction, Theorem 1.3, Proposition 2.1 and Definition 4.1/Theorem 4.2. The sharp 7/9 splitting threshold and balanced three-point examples concern the uniform probability that a pair product stays inside a transversal. This is a two-input test, not the product-weighted relative quadruple test. It provides direct conceptual precedent for carry extremizers but does not by itself establish the theorem here.

### Sparse exact Freiman extension

D. Conlon and W. T. Gowers, *Freiman homomorphisms on sparse random sets*.

https://arxiv.org/abs/1603.01734
Primary author PDF: https://www.its.caltech.edu/~dconlon/homomorphisms.pdf

Inspected the introduction and Theorem 1.2, which concerns exact Freiman homomorphisms from a sparse random subset of a finite abelian group into an arbitrary abelian target. This differs from a hereditary positive-defect infimum for a full-domain map.

### Bracket and floor structure

B. Green, T. Tao and T. Ziegler, *An inverse theorem for the Gowers U4-norm*.

https://arxiv.org/abs/0911.5681

Inspected Section 8 around Proposition 8.5 and the beginning of Appendix C, rather than its complete proof. Bracket-linear structure arising from many approximately preserved quadruples is relevant precedent; it does not give the precise three-residue global arbitrary-target conclusion used here.

V. Bergelson and A. Leibman, *Distribution of values of bounded generalized polynomials*, Acta Mathematica 198 (2007), 155–230.

Author preprint: https://people.math.osu.edu/bergelson.1/BL_GP.pdf

Inspected the abstract, opening definitions and floor-increment discussion. Scalar floor-linear functions are established objects; their occurrence alone is not a novelty claim.

### Pushout algebra

Stacks Project, Tag 05NM: https://stacks.math.columbia.edu/tag/05NM

The target enlargement is standard pushout algebra. Report 291 gives the elementary injectivity and well-definedness proof explicitly and does not advertise a new extension principle.

## Earlier background not newly re-audited in this pass

Report 290's historical comparison also records torsion-sensitive finite-difference literature, including Laczkovich's *Polynomial mappings on Abelian groups* (2004), https://link.springer.com/article/10.1007/s00010-004-2727-9. Only its publisher abstract was available in that earlier pass. The full article and broader group-valued functional-equation literature remain historical leads; no assertion about their complete theorem systems is made here. Earlier project source 56 already used a fixed-weight statistic; project manuscripts establish provenance within the project, not publication priority.

## Search boundaries

The bounded public-source comparison covered respected/image-preserved quadruples, hereditary additive energy, all nonnegative weights, affine/Freiman tests, carry thresholds, floor/bracket-linear structure and fixed-degree fourth-power sampling. Exact searches for the numerical constant and t^4+12t²+6 did not locate an equivalent inspected theorem. Exact-number search has weak evidential value because formulas are poorly indexed.

This was not a systematic MathSciNet/zbMATH review, multilingual review, dissertation search or exhaustive unpublished-work search. Search snippets and secondary aggregators located sources but were not treated as mathematical authority. No equivalent theorem was found among the results inspected; this does not establish originality or priority.

## Claims deliberately excluded

The article does not classify all maps with r=rho, infer a global lower bound from one staircase coset, prove universal finite attainment, extend the theorem to partial domains or nonabelian groups, allow signed/complex test weights, resolve uniform sharp Marcinkiewicz–Zygmund constants, or claim proof-assistant certification. New equality-classification investigations are outside this report.
