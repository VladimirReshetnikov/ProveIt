# Independent source review: quarter-width specialization

The source reviewed has SHA-256
`58588cca492945259d8c30c16e65e18a73597312ae38388b4f2966022c0776b5`.
Its arithmetic correctly derives the imported variable-width threshold
from `w≥1`, `4w≤n`, and `8n≤B`. Indeed `3w+1≤n` and `10w≤3n`; putting
`D=3n−10w` gives `n≤2D`, and the displayed ordered-ring comparisons yield
`2w(n+w)+5w≤BD`. The argument justifies the truncated subtraction before
moving it into the model's difference ring.

The fixed client specializes `B` to `67·8807` and applies the previously
proved same-zero index obstruction. Its conclusion rules out the supplied
`r≤n+w` for a positive symbolic-port graph zero only under the displayed
`w`, `n`, and same-tuple ordinate hypotheses. It does not itself choose a
particular `w`, remove the bound `8n≤67·8807`, exclude all zeros, prove a
reverse guard, or establish an iPRA endpoint.

This is a mathematical source review of the two declarations and their
stated imported interfaces. It is not an independent Lean replay or an
authentication of transitive provider/package ancestry.
