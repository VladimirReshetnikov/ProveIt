# Proposed integration

This delivery is additive. No remote changes have been made.

Suggested report directory:
`Analysis/Polylogarithms/docs/reports/global-radial-monotonicity/`

Preserve `article.tex`, `article.pdf`, `code/`, `data/`, the source inventory, and claim-status documents in the report collection according to the current intake procedure. Replay the verifiers on a scratch copy.

## Canonical manuscript insertion

The namespaced excerpt `05-global-radial-monotonicity.tex` can be inserted after the local-radius material, or after the Cartesian-motion section with a forward reference from the local-radius closing remark. It uses the existing theorem/proof conventions and a new bibliography key `grm:report`. Add the entry from `bibliography.tex` to the manuscript bibliography. No new global LaTeX command is defined by the excerpt.

The excerpt contains proof summaries explicitly identified as such. The complete proofs, constants, and the displayed ten-integer Bernstein certificate remain in the full report. For a fully self-contained canonical treatment, merge Sections 2–5 and Appendix A from the report rather than silently treating the summaries as the entire proof.

## Required status edits

The normalized-radius open-problem remark should read, in substance:

> Full-radius strict decrease is proved for every real a >= 8 and every b > 0. For every a > 0 it is also proved under 2^(-b) < ((2/5)^a-(3/8)^a)/256. For integer a >= 2, the unresolved part is reduced to six bounded b-strips for a=2,...,7. The remaining first-order and fractional parameter cases must be listed separately.

Append the quantitative finite-b theorem after the existing exact `Li_a(z)-z` limit result; retain the earlier result's attribution.

The squared-resolvent/binomial portion belongs with the positive-kernel identities. It does not change the sharp Euler evaluator's status and does not resolve S6/S8.

## Editorial correction

In the transport proof in `05-real-positive-kernel.tex`, use `x=n`, not `q=n`, when applying the Hurwitz formula, and use `q(t)`, not `h`, for its bounded regularized kernel. Check the current surrounding notation and deduplicate against other incoming audit notes.

## Dependency and validation notes

The main a>=8 proof independently establishes its root confinement and uniqueness. The finite-b theorem uses the canonical finite-measure angular uniqueness result (its condition ensures b>8). The cubic criterion uses the known angular derivative sign. Neither positive binomial identities nor the concrete Gaussian certificates depend on the main radial theorem.

The excerpt has been syntax-tested in a minimal article wrapper. It has not been compiled inside a full checkout of the canonical manuscript; cross-file integration and editorial review remain necessary.
