# Report177 source audit

Sources checked on 3 October 2026. This document describes attribution and the limits of the inspected evidence. It makes no global priority claim. The mathematical proofs and finite rational certificates are self-contained in the report and verifier.

## OEIS definitions and credited equivalents

- https://oeis.org/A262810 defines the diagonal alignment count. Its formula section credits the leading equivalent, including the factors exp(-1/12) and exp(-(log 2)^2/24), to Václav Kotěšovec, 23 March 2016. Report177 does not claim that leading equivalent as new. The inspected page did not display the all-orders correction family, column-count theorem, or inverse proved here. It cross-references both A262809 and A316677. The b-file could not be retrieved; no b-file comparison is claimed.
- https://oeis.org/A262809 records the binary alignment array, fixed-row/fixed-column equivalents, and the positive binomial-power sum (Peter Bala, 2018). The exact family and sum are not new.
- https://oeis.org/A316674 was directly accessible and records the nonnegative-entry array relation to A262809. Its diagonal is A316677. The exact unmarked diagonal factor 2^(n-1) is prior; Report177 treats the marked binomial coupling as an immediate corollary of the exact construction. The direct https://oeis.org/A316677 page fetch failed, so no direct page inspection of that entry is claimed.

## Primary papers actually inspected

1. Griggs, Hanlon, Odlyzko, Waterman, *On the Number of Alignments of k Sequences*, Graphs and Combinatorics 6 (1990), 133–146. DOI: https://doi.org/10.1007/BF01787724 . Author-hosted scan: https://dornsife.usc.edu/msw/wp-content/uploads/sites/236/2023/09/msw-096.pdf . The introductory statements and Theorems 1–2 fix k as n tends to infinity. The fixed-dimensional leading theorem does not assert uniformity out to k=n.
2. Pemantle and Wilson, *Twenty Combinatorial Examples of Asymptotics Derived from Multivariate Generating Functions*, SIAM Review 50 (2008), 199–272. Successful primary PDF: https://www.cs.auckland.ac.nz/~mcw/Research/Outputs/PeWi2008.pdf . The UPenn author URL returned 403. Section 4.9 displays the fixed-k alignment constant in clear typesetting. It also corrects two typographical errors in a Waterman handbook expression. Those prior corrections are unrelated to Report177's growing-dimension comparison.
3. Eger, *On the Number of Many-to-Many Alignments of Multiple Sequences*, Journal of Automata, Languages and Combinatorics 20(1) (2015), 53–65; revised https://arxiv.org/abs/1511.00622 (2016). Section 5.5 gives inclusion–exclusion and the positive binomial-product sum, and repeats the fixed-dimensional asymptotic. Section 5.7 concerns a different step set; fixed-dimensional normal approximations elsewhere do not state the growing-diagonal column-count law proved here.

The separate BIBLIOGRAPHY.json gives hashes and byte counts of the exact downloaded primary PDFs used for inspection. These PDFs are not redistributed in the package. The hashes identify the inspected documents; they do not certify every bibliographic claim or the report's analytic proofs.

## Overlap search and limits

A bounded check of the current public ProveIt report catalogue and its full report-subtree filenames found no A262810/A262809 alignment entry. The report subtree had 8,151 entries and its API response was not truncated. An earlier root-tree response was truncated and was not used as exhaustive evidence. Filename absence is not content absence. A bounded search of available prior-report titles and snippets likewise found no exact-ID or relevant alignment-title match; semantic results included unrelated reports. Neither check is exhaustive and neither proves novelty.

The source-backed conclusion is limited: the inspected sources provide the classical exact family and leading fixed-dimensional/diagonal equivalents, but do not supply this report's all-fixed-orders diagonal polynomial family, n/4 column-count shift, and inverse construction. Independent literature review would be needed before making a publication-level priority claim.

## Claims expressly outside the report

No global novelty, complex-parameter uniformity, local CLT, Berry–Esseen rate, effective remainder constants/onsets, exact universal single ceiling, convergent infinite series, or exponentially improved counting expansion is asserted. Exact rational finite checks establish the stated finite identities and bounds, not the analytic all-orders theorem.
