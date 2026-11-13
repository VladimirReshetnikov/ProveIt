# K control block sum: source-only draft

This uncompiled source proposes to split the symbolic Fin44 control vector
using the generic shifted `Fin.append` sum theorem, remove the two zero-gap
blocks, and show that the remaining sum equals the actual four control sums.
It separately transfers the pointwise symbolic-to-literal vector equality to
the weighted sum. It depends on the independently audited generic append
client and symbolic-block vector client. No guarded run or Lean result exists for this source;
external coefficient-array and file binding remain separate.

Source SHA-256:
`08a88e2b0cdf7b27dc0b2d53e7203574bf0f0bc3c4d343d882ad68d1d80c25cc`.
