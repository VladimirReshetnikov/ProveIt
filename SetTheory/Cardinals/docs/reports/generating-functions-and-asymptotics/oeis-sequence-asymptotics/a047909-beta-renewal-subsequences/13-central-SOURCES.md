# Sources and bounded provenance

Checked 2 October 2026. See `source-hashes.json` for hashes of inspected external sources. The full external documents are not redistributed.

## Primary mathematical sources

1. OEIS A047909: https://oeis.org/A047909. Multiplicity m is the row index, alphabet size k is the column index, and the upward antidiagonal d is H(d,1), H(d−1,2), …, H(1,d). Row m=2 begins 1,5,47,641,11389; column k=2 begins 1,5,19,69,251.
2. OEIS A268485: https://oeis.org/A268485. The diagonal is a(n)=H(n,n), with a(0)=1. Machine-readable source records were inspected in the official oeisdata GitHub repository; their URLs and SHA-256 hashes are recorded without redistributing the source records.
3. J. D. Horton and A. Kurn, “Counting sequences with complete increasing subsequences,” Congressus Numerantium 33 (1981), 75–80. Original not obtained in full. Exact enumeration was consulted through Theorem 2.1 of source 4. No absence-of-asymptotics claim about the unseen original is made.
4. Alexander Clifton, Bishal Deb, Yifeng Huang, Sam Spiro, and Semin Yoo, “Continuously Increasing Subsequences of Random Multiset Permutations,” European Journal of Combinatorics 110 (2023), 103708. DOI: https://doi.org/10.1016/j.ejc.2023.103708. Preprint: https://arxiv.org/abs/2110.10315. Inspected full author-hosted March 1, 2023 version: https://yifeng-huang-math.github.io/files/paper_cont_inc.pdf. Its Gaussian and moment conjectures must be read alongside source 5.
5. Yassine El Maazouz and Jim Pitman, “The Bernoulli clock: probabilistic and combinatorial interpretations of the Bernoulli polynomials by circular convolution,” Combinatorics, Probability and Computing 33 (2024), 210–237; online 16 November 2023. DOI: https://doi.org/10.1017/S0963548323000421. Preprint: https://arxiv.org/abs/2210.02027. Full arXiv text inspected. Proposition 5.2 and Section 5 give the independent Beta increment mechanism; Proposition 5.13 proves the Gaussian limit. Neither the exact renewal law nor the Gaussian limit is claimed as new here. Different stopping-index conventions are avoided by defining all formulas directly through p_m(k)=P(B1+…+Bk≤1).

## Search limits

Searches used the exact sequence IDs and complete/continuously increasing subsequence title phrases, combined with renewal, normal, Edgeworth, asymptotic and dates 2024–2026; “Bernoulli clock” with Edgeworth/renewal/asymptotic; and Beta(1,m) with Edgeworth. No later explicit quantitative central or inverse-threshold treatment was located in this bounded search. This does not exclude an older general triangular-array or renewal theorem that implies an expansion after routine hypothesis verification. The report's contribution is the explicit specialization, coefficients and controlled proofs, rather than a claimed new general method or a comprehensive novelty certification.

## Scoped ProveIt overlap check

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: 4b874cea0012c51a6841ad9c58f6e20fa57c71da

The audit was read-only. It inspected the nontruncated SetTheory subtree (5,973 entries), the exact OEIS-asymptotics directory (25 directories), all 92 Markdown/TeX files in that scope, the full 177,611-byte report manifest, and 71 relevant text members from six incoming archives plus the incoming README. There were no failed downloads in the focused 92-file scan. Candidate identifiers and mechanism terms returned no hits in this scoped content.

The exact report scope was `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics`. The search did not claim that every file in the repository was fetched. A globally recursive tree is known to truncate, so the conclusion rests on specifically scoped nontruncated trees and content scans. Nearby Fourier-peak and dyadic-rigidity reports concern different mechanisms.

These source and overlap checks support only the bounded wording used in the article. They cannot prove universal historical novelty.
