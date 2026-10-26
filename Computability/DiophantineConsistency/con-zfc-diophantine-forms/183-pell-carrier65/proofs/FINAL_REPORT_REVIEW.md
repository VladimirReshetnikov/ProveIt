# Final report and release review

Production note: after this review, the contents depth was set to one to keep the contents on one page, and the appended equation page explicitly suppresses the report header. These changes affect layout only. verification/production.json binds the final report bytes.

Independent reviewer: `/root/direct_construction`.
Date: 25 October 2026 (client date).
Verdict: **PASS. No serious mathematical or scope correction identified.**

## Scope read

The reviewer read the complete final `report.tex`, including the whole coefficient recipe, the reverse-discovery packing argument, both domain translations, the verification/scope sections, bibliography, and the 65-row evaluator appendix. The release `README.md`, `verify.py`, `code/build.py`, `code/coefficients.py`, and `code/domain_translations.py` were also inspected.

At the time of the transcription check, the report-source SHA-256 was

    b03703c20d950cb78ddaee874e002597c396990b20769e3a55740f0fcfa002e5

The review is an independent internal AI-assisted mathematical and transcription review. It is not an external human endorsement or a proof-assistant certification. Rendering, typography, page fit, and local PDF/text-size measurements remain separate visual/production checks.

## Mathematical findings

1. The report uses exactly fourteen independent positive variables. Every other displayed quantity is a polynomial abbreviation; all variable exponents are fixed. The four large fixed integers are specified by a finite, closed recipe.

2. The elementary consecutive-product Pell lemma is correct, including the report's simplified negative-norm descent. For norm minus one and m>=2, the inequalities m*y<x<(m+1/2)*y directly force the transformed ordinate into 0<y'<y; taking the absolute value of the transformed first coordinate is legitimate and avoids an unnecessary positivity sublemma. The norm-one descent correctly terminates at (1,0), yielding fundamental unit (2m+1)+2*sqrt(m(m+1)).

3. The sign recovery is noncircular. The proof cancels the universally positive Delta, excludes the four negative norm units, obtains Nt=1, derives C>0, bounds R, and only then proves the substituted trace tau positive.

4. The exact rank estimates are correct:

       q(q^2-1)<R<q^4-q^3,
       E>=q^4,
       tau>k+2>0.

   The upper-bound cancellation printed in the report was independently checked.

5. The omitted h is integral by the first-root congruence modulo E. The proof of strict positivity treats both possible Pell-rank cases and does not infer positivity solely from divisibility.

6. The soundness map inserts positive h and tau into the exact parent equation. Completeness uses canonical parent witnesses only. The report correctly separates this sufficient existence-equivalence argument from the optional stronger all-zero bijection.

7. The interpretation of Con(ZFC) is syntactic and internal to the theory. The report neither assumes consistency nor claims to decide it. The newly written arithmetic argument is clearly separated from the inherited native/K215/refutation calibration, and no fresh end-to-end Lean/Rocq proof is claimed.

8. The 65-operation calculation and exact degree 150 are correct. The full leading homogeneous form and the selected coefficient -8*beta^88 agree with the independent audit. The main-norm cancellation is accounted for explicitly.

9. The reverse-discovery packing lemma is correct, including radix-one discoveries, the stored halt digit, the outer reduction modulo H+1, the extraction of the auxiliary flag field, and empty-prefix conventions. The actual decoder's finite identity checks passed for all 430 actions and 942 tiles.

10. Both domain translations are correct. Successor translation gives 14 natural variables, 79 operations and unchanged degree 150. The ternary quadratic onto map gives 42 integer variables, 163 operations and exact degree 300. The degree-doubling argument uses an injective doubled-exponent specialization and is sound.

11. The fixed coefficient tuple is unchanged pointwise. The distinction between fixed integer leaves, fully expanded coefficients, arithmetic operation count, and bit complexity is maintained.

## Literal transcription and replay

A separate transcription check parsed every printed evaluator row in the report appendix and compared the resulting operations with `equation/carrier65.json`: all 65 rows agree, in order. It also extracted the report's 399 numeral characters and compared them with `equation/SEED.txt`: exact agreement.

The receipt is `FINAL_REPORT_TRANSCRIPTION.json`.

The release verifier was independently run as

    python3 -B verify.py --skip-manifest --receipt <external-review-directory>/FINAL_RELEASE_REPLAY.json

It passed. This run checked source pins, all 430 actions and 942 indexed tiles, all four actual coefficient integers and hashes, the scalar interface, eight byte-identical reconstructed files, primary arithmetic structure and degree, both domain-companion constructions, the independent seed checker, and deliberate corruption controls.

The skip-manifest option was appropriate during final report production; this review does not represent that run as a final sealed-manifest verification. The separate final package sealing/check is the root agent's responsibility.

## README and verifier scope

The README describes the result as a strict improvement of a matched parent and explicitly acknowledges other variable/degree/cost regimes. It credits the related quotient-carrier and mixed-radix work, and does not claim literature-wide priority or global minimality.

The verifier's positive claims concern finite artifacts, identities and transcription. Its outputs do not claim to establish the unbounded calibration by testing examples. The source-pin count and optional release-manifest check are explicit. The mathematical proof and finite verification remain properly distinguished.

The standard-library statement is correct: the independent arithmetic checker contains its own sparse Polynomial implementation and has no SymPy or other third-party dependency. The report's mention of all 65 operations and 14 live positive inputs is supported by the independent checker. Inspection of the explicit domain-substitution constructor shows that the companion inputs and new gates feed those same live parent inputs.

No additional mathematical change is requested before release.

