# Compiled report review — Round 18

Review date: 25 October 2026. Scope: compiled article, all seven report TeX files, released endpoint metrics/coefficients, and the four separate ordinary mathematical reviews in this directory. This is an internal artifact and mathematical-consistency review, not external human peer review or a new full-kernel certificate.

## Status

**PASS — final compiled article, all 22 pages; all reported issues resolved.**

The reviewed initial PDF was `round18/render/main.pdf`, 21 letter-size pages, SHA-256 `2c5953aa3711f94dc5193d8a901fc901750b43cbe6e0be1e94cc4af1944f9650`. Every page, 1 through 21, was rendered with Poppler and visually inspected, not only text-extracted. PNGs are in `review/rendered_report/`; extracted text is in `review/report_text.txt`.

## Corrections reported immediately (first two now resolved)

1. **Page 14, third-auxiliary exclusion display.** `compact_section.tex`, line 163 in the initial copy, contains `c-c_3,qquad` instead of `c-c_3,\qquad`. The PDF visibly prints the letters `qquad` as mathematical variables between the two equations. Restore the missing backslash (or use separate gathered lines), then recheck the rendered page.
2. **Page 11, executable option.** `natural_section.tex`, line 336 in the initial copy, has `\texttt{verify.py --rebuild}`. The compiled PDF and extracted text turn the two option hyphens into an en dash. Use `\texttt{verify.py -{}-rebuild}` or verbatim text so the printed/copyable command has two ASCII hyphens.

No other clipped/overlapping text, overwide mathematical display, misplaced equation tag, unreadable table, missing glyph, or broken page boundary was found. The 21-page pagination is coherent, including the two-page contents and the split proof paragraphs. The third compile log has no overfull/underfull/undefined-reference warning. The coefficient code is small but legible and unbroken within each printed row.

## Finite artifact cross-check

I independently expanded every residual square and collected every coefficient for all five final integer quartics and all three final natural quartics, without importing a producer or verifier. Every result exactly matches its literal `expanded_polynomial.json`, with no duplicate collected monomials, and has the following metrics `(variables, rows, degree, terms, height)`:

- integer278: `(278, 188, 4, 12884, 12227)`.
- integer279_balanced: `(279, 189, 4, 5483, 7200)`.
- integer279_sparse: `(279, 189, 4, 5202, 12662)`.
- integer284_sparse: `(284, 194, 4, 4270, 10864)`.
- integer306_sparse: `(306, 216, 4, 3870, 14512)`.
- balanced229: `(229, 179, 4, 5607, 65892965)`.
- low_height228: `(228, 178, 4, 9522, 560804902)`.
- sparse228: `(228, 178, 4, 7512, 2445412949744)`.

These agree with both article tables and all reported summaries. The compact release's six operation/degree records agree with `77/626`, `78/464`, `78/622`, `79/460`, `79/518`, `80/384`; the article correctly identifies `78/622` and `79/518` as dominated controls and explicitly rejects `81/410` and `82/304`. The root records agree with `(14,86,112)`, `(14,94,110)`, `(14,88,115)`, `(13,156,125)` and the article distinguishes new reductions from exact recompilations.

The entire printed 436-character BFS943 coefficient code matches the reconstruction program byte for byte. The displayed finite decoder, indexed tiles, and coefficient formulas agree with the inspected reconstruction code. Its four bound payload bit lengths agree with the largest-port claim of 592,884 bits. Compact and source34 tuples are explicitly kept separate.

Machine-readable records: `review/report_metric_crosscheck.json`.

## Mathematical/editorial consistency

I read the complete quartic, natural, compact, and root ordinary mathematical reviews and checked the article against their accepted arguments and restrictions. No additional mathematical discrepancy was found.

- Integer residual shears, affine projections, restoration order, and finite row-span obstruction match the reviewed reductions. The 278-variable result is a support tradeoff, not falsely a domination result. The rank obstruction is expressly confined to the current rational row span.
- Natural variables are nonnegative, not unrestricted integers. Bootstrap positivity precedes factorial decoding; root-modulus divisibility is established before the first binomial; the descending CRT sign is correct. The article preserves the positive restoration and cofinal-anchor chronology. Row shears preserve the common zero set, not polynomial equality.
- The repaired compact partial chart is `Y=q^2 s`, `D=q^3 Y`, with the correct reused numerator `H{h(Y^2-e)-DB}` and `D sigma=Y^2`. The proof does not infer integral padding too early, does not assert false `gcd(Y,h)=1`, and uses the small-index modulus before full denominator recovery. Both signed third auxiliary branches and positive completeness are retained. All six highest homogeneous forms match the review.
- The root merger uses the nonzero odd carrier and applies only after its other denominator is nonzero. The unit-product exclusions, literal parent-zero restoration/lifts, `I=0` branch, exact degrees, and pointwise compiler-only savings match the reviewed proof. The previously disclosed leading-form correction is attributed as such, not claimed as a new discovery.
- Ordinary arithmetic/native/C222/ZF/ZFC calibrations remain identified inherited dependencies. The article does not turn finite checks into a consistency/nonvanishing proof, global optimum claim, external peer-review claim, or fresh end-to-end proof-assistant endpoint.

## Final-change recheck scope

Recheck page 11 after the command-option correction and page 14 after the missing-backslash correction. A new radix-55 note inserted near the final reproduction section would require re-rendering page 21 and any overflow/new pages; if inserted into the natural section, recheck that insertion page and every later page whose pagination changes, plus the contents pages for updated page references. Any change to equations or claimed theorem scope additionally requires content review, not only visual inspection.


## Second-candidate recheck (22 pages)

The appendix addition moved the report to 22 pages. All newly changed pages 2–8, 11, 14, 21 and 22 were visually re-inspected; pages 1, 9–10, 12–13 and 15–20 initially had identical rendered pixels to the already inspected pages. Both original findings are resolved: page 14 has the intended mathematical spacing, and page 11 now prints and extracts `verify.py --rebuild` with two ASCII hyphens.

Build 5 still had a changed-label warning and stale contents references. I requested another compile. Build 6 has no overfull, undefined, changed-label, or other warning. Only page 1 pixels changed from build 5; I visually inspected it and verified the corrected contents page numbers. The build-6 PDF hash is `a4528d8a219d20f41fca35c412b0c8e22b2d5a8ae6d2d08c6a9d083c2957f9c4`. All 22 pages are thus visually covered, with pixel equality used only to avoid re-inspecting unchanged pages.

The radix55 storage claims were independently checked from the actual decompressed payload bytes: 295,388 versus 242,484 bytes; 592,884 versus 486,696 largest-port bits. The whole sidecar proof and the separate `compact_radix55_math_addendum.md` were read. The note preserves whole-tuple specialization, distinguishes the specialized polynomials, credits the accepted upstream encoding, and does not claim a printed-page/PDF-byte gain.

One final notation issue was reported in the article appendix: after introducing the fresh `A_source=Y(X+1)+2`, it writes `S=Delta i c²` and `Ns=Delta` without distinguishing the pre-existing +1-base reduction quantities. The full sidecar proof correctly uses fresh `Delta_source=A_source²-1`, `i_source`, and `c_source`. The article should give those quantities fresh subscripts explicitly; this is a report-summary correction, not a newly discovered defect in the reviewed sidecar bridge. Recheck page 22 after correction and verify the final staged PDF matches the final rendered candidate.


## Final sign-off

**PASS for the final build-8 PDF**, 22 pages, 431,614 bytes, SHA-256:

`d75928afb7d05d54c243bb50162cd652135d861ff59da1f7b880b0a25ca0a4a1`

Only page 22 rendered pixels differ from the fully inspected/stable build 6. I visually inspected the final page and verified that `Delta_* = A_source²-1`, `i_*`, `c_*`, `S=Delta_* i_* c_*²`, and `Ns=Delta_*` are explicit and distinguished from reduction-chart witnesses. The fresh notation now agrees with the full bridge proof and its separate ordinary mathematical addendum. The new line wrapping is clean. The final build log has no overfull, undefined-reference, changed-label, or other warning.

Final rendered evidence: `review/rendered_report_final8/page-01.png` through `page-22.png`; final text: `review/report_text_final8.txt`. Every final page is covered by direct visual inspection or exact pixel equality with an already directly inspected page. Both original typographic corrections remain resolved, final contents references are stable, all eight expanded quartic coefficient checks pass, and no substantive mathematical/editorial discrepancy remains in this report review.

Packaging handoff verified at 21:01 UTC: the staged `round18/package/ConZFC_Residual_Bases_Denominator_Engineering/report/main.pdf` is byte-identical to the approved build-8 render and has the same SHA-256 above. The formerly stale staged copy has been replaced. No report issue remains; the parent owns final package sealing.
