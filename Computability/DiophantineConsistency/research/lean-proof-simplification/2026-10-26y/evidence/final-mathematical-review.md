# Independent mathematical and evidence review

Reviewed on 26 October 2026 against production source commit
`553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.

Scope: the report's P2, P3, P4 and P6 arguments; exact source assumptions;
existing proof fixtures and validation records; raw line-count and integration
claims. This review did not run additional experiments or audit novelty.

## Conclusions

- **P2:** The helix hypothesis is exactly periodicity by `(w, -1)` on
  `Int × Int`. Its integer multiple by `t` sends `(x, t)` to `(x + t*w, 0)`.
  No positivity, least-period, or vertical-period hypothesis is needed.
  The isolated replacement retains the original theorem's full generality.
- **P3:** Translating the left seam by the positive period puts another seam
  inside the open strip if `N < L + R`, giving the claimed contradiction.
  Positivity follows from `InitialStrip.left_pos` and `left_le`. Equality at
  the right endpoint is allowed. `L ≥ 1` and `R ≥ 2` then imply `N > 2`.
  The generic integer kernel has a successful receipt. The copied-source
  fixture did not finish, so neither it nor the production adapter should
  be described as Lean-validated.
- **P4:** The output threshold determines the pairing branch under the four
  original semiring/order classes. Nonnegativity is essential in the false
  branch. The discrete successor-order premise is retained where equal
  outputs imply equal shell maxima; the new threshold helper itself does
  not need that premise. The fixture preserves the original abstract scope.
- **P6:** `mul_geom_sum` supplies the integer identity without a sign
  hypothesis. For `B ≥ 2`, nonnegativity of the preceding geometric sum and
  `(B - 2)` yields the stated strict upper bound, including `d = 0`.

The report distinguishes physical source-line comparisons at the pinned
commit from hypothetical savings after every previous proposal is applied.
It charges the new P4 helper to the whole-file count and distinguishes
isolated proof checks, generic kernels, and production integration.

Two textual corrections were identified for final assembly: attribute
`rowSupportIndices` to `NativeQuadraticParent`, and remove completed-check
wording from the unfinished P3 copied-source fixture and its notes. No
mathematical correction was requested for P2, P3, P4 or P6.
# Final packaging follow-up

The independent read-only review also checked the final `VALIDATION.json`,
`source-targets.json`, TeX validation summary, README, and replay script.
Their nine successful check entries agree on scope: P3 is generic-core-only;
the seven headline candidates are not full-module builds; the supplementary
Sidon candidate is the full-module exception. The replay core filename and
working-directory instructions were corrected after that review. No additional
Lean runs were performed for this packaging check.

