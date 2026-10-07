# Source register

Access date: 2026-10-07. The research uses selected repository material; it is not an audit of all manuscripts or all formal proofs.

## Repository snapshots

### openai/math

Commit observed through the GitHub connector:

```text
adc7f1241b42e322a6451854ab7e4b4c146bf78a
2026-10-06T21:58:50Z
```

- Repository: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
- README: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/README.md
- Catalogue: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/overview.tex
- Selected manuscript: `preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/`
- Selected source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/build/sections/03-relative-detection.tex
- Selected source blob SHA: `ca82af70203a4d9d18371266741b8b7210e658d9`.

The specific target is the “Bounded-grid moments” lemma, source label `ap:path:grid`. Its hypothesis is 1 ≤ q ≤ j. The following relative-cube argument uses these grid moments for densification. The source's global quasipolynomial progression theorem is motivation only and is not used as an established theorem.

### VladimirReshetnikov/ProveIt

Snapshot observed through the GitHub connector:

```text
fb9602e556560a15704b4feb176ba6de08378665
2026-10-07T19:43:57Z
```

- Repository: https://github.com/VladimirReshetnikov/ProveIt/tree/fb9602e556560a15704b4feb176ba6de08378665
- Research overview: https://github.com/VladimirReshetnikov/ProveIt/blob/fb9602e556560a15704b4feb176ba6de08378665/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md
- Relevant directory tree observed: `3475c8cf4c60257d8320f8c28e3e1f3e9d48987e`.

The overview supplies research context: density transfer, phase partitions, inverse steps, moments, and configuration counts. It explicitly says that research placement confers no formal status. The present package is a standalone finite-field study, not an extension of the existing proof ledger by assertion.

## Classical literature

1. W. T. Gowers, *A new proof of Szemerédi's theorem*, Geometric and Functional Analysis 11 (2001), 465–588. DOI: https://doi.org/10.1007/s00039-001-0332-9 . Background context; no deep quantitative theorem from it is needed in the new proofs.

2. W. T. Gowers and J. Wolf, *The true complexity of a system of linear equations*, Proceedings of the London Mathematical Society (3) 100 (2010), 155–176. https://arxiv.org/abs/0711.0185 ; https://doi.org/10.1112/plms/pdp019 . Conceptual predecessor for the relation/tensor-independence viewpoint. The article does not claim the full modern true-complexity theorem as a result of this one paper.

3. D. Conlon, J. Fox, and Y. Zhao, *A relative Szemerédi theorem*, Geometric and Functional Analysis 25 (2015), 733–762. https://arxiv.org/abs/1305.5440 ; https://doi.org/10.1007/s00039-015-0324-9 . Inspected arXiv version 2, including Definition 2.8 and Sections 6.2–6.3. The PDF's linear-forms diagram was also inspected. Used to explain why enlarged patterns and subproducts matter; not used to assert a new general sparse counting lemma.

4. E. Ghorbani, S. Kamali, G. B. Khosrovshahi, and D. S. Krotov, *On the volumes and affine types of trades*, Electronic Journal of Combinatorics 27(1) (2020), P1.29. https://arxiv.org/abs/1810.02296 ; https://doi.org/10.37236/8367 . Identifies the classical minimum-volume and code-theoretic context. The finite-field support argument needed here is proved directly.

## Novelty search record

Targeted searches included combinations of:

- symmetric matrices, equal/constant diagonal, rank distribution, finite fields;
- quadratic cube rank enumerators;
- finite-field weighted Laplacians, graph girth, bilinear moments, and convergence rates;
- matroid closure and quadratic moments;
- grid relations, trades, tensor independence, and relative counting.

These searches did not identify the exact closure-correction theorem, graph-girth moment law, or the full cube enumerator proved here. Most matrix-search hits concerned unrelated real matrix completion or coding problems. No absence-of-prior-art conclusion follows from this limited search, and unrelated search hits are not mathematical dependencies.

## Redistribution

The package includes no copies of the third-party manuscripts, no copied repository source trees, and no font files. The bibliography and this register provide references; the new proofs and verification code are supplied directly.
