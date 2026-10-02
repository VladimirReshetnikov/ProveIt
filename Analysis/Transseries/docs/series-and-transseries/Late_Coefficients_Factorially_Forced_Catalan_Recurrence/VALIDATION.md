# Validation summary

## Scope

The article is a mathematical proof with supplementary exact and numerical checks. It is not a formally verified proof, an exhaustive originality certificate, or a package of numerically certified asymptotic error constants.

## Analytical review

The factorial-series application, exact Stirling transform, uniform weighted-Fubini estimate, lower-tail bounds, beta-integral moments, finite Watson remainders, correction formulas, and late-coefficient inverse have been reviewed independently. The positive factorial half-truncation and scalar expansion have also received separate independent reviews. A fresh integrated mathematical and source review of the complete final manuscript passed without required corrections. It also checked the original-sequence inverse, the half-truncation scalar proof, and the rational lower-bound corollary. Independent finite calculations reproduced the correction coefficients, 560 rational lower-bound checks, and the displayed high-precision inverse values.

## Computation

- Exact recurrence data and independent differential-generator/Stirling checks through index 500
- Literal binomial D/H checks through degree 40
- Two exact generators for the first six late-coefficient corrections
- All 24 displayed A229741 and 21 displayed A260879 terms matched
- Decimal normalized ratios stable at 80 and 100 digits
- Late-coefficient and original-sequence smooth inverse checks at indices 100, 300, 600, and 1000, stable at 80 and 100 digits
- Exact half-truncation complement and finite-shape identities for n=2,...,64
- Nine exact even/odd scalar remainder corrections, with illustrative exact-rational remainder evaluations through n=1001

## Presentation

All 16 rendered PDF pages were visually inspected. The final bibliography-size change was re-rendered and inspected; it removed a two-line spill to a seventeenth page without changing mathematical text. No clipping, overlap, missing glyphs, unresolved references, or overfull-box warning remained. Extracted PDF text contains no unresolved double-question-mark references.

## Replay

The package is designed for ordinary Python ZIP extraction followed by `bash replay.sh`. Full replay regenerates all 12 recorded data files and the PDF; binary PDF identity depends on the same TeX environment. An actual Python ZIP extraction followed by `bash replay.sh` completed successfully: all 27 manifest entries were verified, all 12 regenerated data files were byte-identical to the recorded files, and the rebuilt PDF was byte-identical in the tested TeX environment.

## Reviewed artifact digests

- Main TeX SHA-256: 26b1ab3dba16e2991a3111e746cabc351d2b60fc2cbf4c2a31aeac528f36ab50
- Auxiliary numerical table TeX SHA-256: bf4517bdce1f5e5ff67a5be98f3ce8e7b17fd6e8494d673aad4f8ada75439dd7
- PDF SHA-256: 94c977303a447c755984b997906487c0fcb759c4a04b3678bedca2ef52fcb2a1

The manifest covers all distributed files apart from itself. The ZIP's own digest is supplied separately at delivery, avoiding a self-referential hash.
