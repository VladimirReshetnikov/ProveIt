# Mechanical four-stage sum-prefix split

`split.py` pins and mechanically separates the six unchanged theorem blocks in the [group02 source draft](../nine-seed38-jones-prefix-group02-draft/README.md) into four modules: the three B-preservation lemmas, then one module each for the symbolic star sum `e`, short range sum `ell`, and geometric range sum `lambda`. Its no-Lean `--check` passed. The finite sums, powers and seed-derived coefficients stay symbolic; no range is enumerated by this source split.

All six proofs are uncompiled. Splitting helps retain stage-specific failures and avoids requiring all three sum lemmas in one source module; it does not establish resource fit or full-recipe entry identities. The split generator SHA-256 is `3e383bfe57f0315d83c791359a66a90c4847eb8f42c60f26a0028fb98ab2111b`. The source-only candidate makes no full semantic equality, JSON/document binding or operation-count claim.
