# Sources and provenance for Report 294

## Mathematical provenance and theorem dependency

Report294 proves the target-sensitive 5/9 upper bound when multiplication by two on the target is injective, including the Q=45 order-nine branch and Q=41/Q=39 exclusions. It supplies a complete qualitative all-rank gluing proof and the complex three-fiber SOS/Fourier lower argument giving weighted and indicator attainment at every fixed positive rank.

It also proves the exact real and complex fourth-power norm ratio for R_9=I-2J/9, including all nonzero real equality vectors. Nine-frequency Fourier blocks and product factorization then prove that codimension-two LINEAR pullback spikes have weighted energy infimum lambda for every fixed source of dimension at least two and every fixed target with nonzero two torsion, including infinite-dimensional sources with finitely supported weights.

The arbitrary-target upper bound r(a)<=lambda is explicitly imported as Theorem 1.4 in this report from Theorem 1.2 of Report293, The Sharp Weighted Energy Gap on Elementary Abelian Three-Groups, prepared for Vladimir Reshetnikov, 7 October 2026. Its complete plane upper argument and gluing proof establish that statement for arbitrary targets. Report294's own gluing proof is reproduced and rephrased for the sharper target-restricted use. The preceding weighted universal theorem is a visible mathematical dependency, not a hidden software input.

Frozen Report293 TeX SHA-256:
82c4452ac6ac25551b39802e673cc1dbfabfc336d2b78024e001b0d9f62e92ba

The two separately checked research proof revisions underlying the new arguments had the following SHA-256 identifiers:

- Sharp 5/9 gap without nonzero two torsion: a5aac7f755a5b61528c4a269e731ecdccf5a9233e7a41747b9d85c8dff2b950c
- Sharp higher-rank order-two spike lifts: a7e6f697a68e60db8bc6b2ee7a050da2353cce2eabb6ec8a0aac0647bf5b0d75

Those working files are not distributed or required for replay. Their substantive arguments are in the manuscript; the exact finite relation witnesses needed for the proof are distributed. Report293 and all earlier files remain unchanged.

## Exact public inventory

1. README.md
2. REPRODUCING.md
3. SOURCES.md
4. Report294.tex
5. build.py
6. companion/__init__.py
7. companion/README.md
8. companion/exact_checks.py
9. companion/midpoint_certificate.json
10. tests/test_build.py
11. tests/test_companion.py

The PDF makes twelve public nonmanifest files. MANIFEST.sha256 lists those twelve and not itself. The ZIP therefore contains thirteen entries. Logs, build receipts, page renders, research notes and private review records are excluded.

## Builder and certificate provenance

The guarded builder and its test suite are adapted from the frozen Report293 public distribution, with report-identity/archive-name changes and the certificate filename substitution. The source counts, no-follow snapshotting, exclusive-output rules, resource bounds, subprocess isolation, source-immutability checks, normal/optimized comparisons, PDF gates and deterministic ZIP logic are preserved.

Report293 builder SHA-256:
6dd7f1533625fe0d65ebc087adf8181d2ea7e7db54c0512ff73aeddf4e74f942

Report293 builder-test SHA-256:
812c245a7a85dd43f95de5f2ec699320145fb740b5dde5fabc74e3b34b25eb35

The mathematical companion contains all Report294 proof-algebra identities, exhaustive symbolic midpoint certificates and separately labeled finite examples. Its README documents the inherited sparse-polynomial implementation patterns and the original audit-data hash. No earlier module is imported. The midpoint verifier checks direct integer linear combinations; there is no HNF, computer algebra system, numerical optimizer or network dependency. Its exact scope and validation budgets are in companion/README.md.

## Primary literature and inspection scope

The URLs below were checked against primary preprints, author or institutional records, publisher records or DOI destinations on 7 October 2026. They are context and attribution, not hidden premises of the energy theorem. The comparison is bounded, with no novelty or publication-priority claim.

### Constant off-diagonal matrix norms

L. Bouthat, A. Khare, J. Mashreghi and F. Morneau-Guerin, The p-norm of circulant matrices, Linear and Multilinear Algebra 70 (2022), 7176-7188.

- https://arxiv.org/abs/2109.09728
- https://doi.org/10.1080/03081087.2021.1983513

The full primary preprint's relevant definitions and Theorems 3.2, 4.1, 5.1 and 5.2 were inspected. The mixed-sign instance -R_9=A(9,-7/9,2/9) gives the applicable upper bound sqrt(23)/3. The nonnegative-entry formula does not apply.

K. R. Sahasranand, The p-norm of circulant matrices via Fourier analysis, Concrete Operators 9 (2022), 1-5.

- https://arxiv.org/abs/2111.11389
- https://doi.org/10.1515/conop-2021-0123

Relevant primary theorem statements inspected; the mixed-sign estimates do not give the exact displayed reflection constant merely from Fourier diagonalization.

L. Bouthat, J. Mashreghi and F. Morneau-Guerin, On the norm of normal matrices, RIMS Kokyuroku Bessatsu B93 (2023), 183-222.

- https://r-libre.teluq.ca/2603/
- https://r-libre.teluq.ca/2603/1/B93-10.pdf

The institutional record and indexed primary passages around Conjecture 5.6 and Proposition 5.7 were inspected. Full-PDF retrieval did not succeed, so this is not a full-paper audit. The real equality theorem in Report294 verifies the conjecture's two-coordinate-value prediction for this particular parameter instance. No claim about the general conjecture's present status or the prior unresolvedness of this instance is made.

C. Riener, On the degree and half degree principle for symmetric polynomials, Journal of Pure and Applied Algebra 216 (2012), 850-856.

- https://arxiv.org/abs/1001.4464v2
- https://doi.org/10.1016/j.jpaa.2011.08.012

Theorem 1.3 in the primary preprint (page 2) was inspected directly. Its attribution to Timofte and the symmetric-quartic two-valued test were verified. The report explains the derived norm-attainment reduction, separately from all-maximizer classification.

### Centering and complexification

E. Shargorodsky and T. Sharia, Sharp estimates for conditionally centered moments and for compact operators on Lp spaces, Mathematische Nachrichten 296 (2023), 368-381.

- https://arxiv.org/abs/2008.06925
- https://doi.org/10.1002/mana.202100217

Theorem 2.1 and the discussion of finite uniform centering were inspected. The centering operator I-P is different from the reflection I-2P; no exact reflection reduction was found in those inspected results.

O. Holtz and M. Karow, Real and complex operator norms, manuscript dated 2004, posted 2005.

- https://arxiv.org/abs/math/0512608

Theorem 3.1, Lemma 3.4 and the postscript were inspected. They cover the real-to-complex p=q=4 step and point to earlier publications of the result. Complexification is explicitly treated as classical in the report.

### Moment bounds

K. Pearson, Mathematical contributions to the theory of evolution, XIX. Second supplement to a memoir on skew variation, Philosophical Transactions of the Royal Society A 216 (1916), 429-457.

- https://doi.org/10.1098/rsta.1916.0009
- https://upload.wikimedia.org/wikipedia/commons/c/ce/429-PTRSA-216.pdf

Original pages 432-433 were inspected for beta_2 >= beta_1 + 1; the footnote credits the displayed proof to G. N. Watson. The report gives its own full square expansion.

W. Kirby, Algebraic boundedness of sample statistics, Water Resources Research 10(2) (1974), 220-222.

- https://doi.org/10.1029/WR010i002p00220

The primary abstract was inspected for the sample-skewness bound (n-2)/sqrt(n-1). The full proof was not obtained; the report supplies the complete nine-atom Lagrange-multiplier argument and equality details. The normalization uses central moments with divisor n.

### Additive energy context

W. T. Gowers, A new proof of Szemeredi's theorem, Geometric and Functional Analysis 11 (2001), 465-588.

- https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

The preceding literature review inspected Sections 6 and 14, including graph energy, the all-weight product-property definition and Lemma 14.2. The report distinguishes that normalization from ordinary additive energy and makes no direct global Ramsey or Szemeredi improvement claim.

## Historical boundaries

No exhaustive MathSciNet/zbMATH review, forward-citation search, multilingual or dissertation search, or unpublished-work review was performed. No first-use claim is made for graph energy, universal nonnegative weights, local-to-global geometry, moment inequalities or complexification. No proof-assistant formalization is asserted.
