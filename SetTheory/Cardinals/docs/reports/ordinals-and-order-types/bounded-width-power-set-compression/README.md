# Bounded-Width Power-Set Compression

This package contains a 21-page research manuscript proposing and studying a
finite/infinite problem at the intersection of extremal combinatorics,
choiceless set theory, and formal mathematics.

## Files

- `article.tex` — complete LaTeX source.
- `article.pdf` — compiled US-Letter PDF.
- `verification.py` — standard-library Python verifier for the finite
  constructions and numerical tables.
- `verification_report.txt` — exact output of the verifier.
- `SHA256SUMS.txt` — cryptographic checksums of the four principal files.

## Main results

The manuscript defines an `r`-width compression of a poset to be a map whose
every fiber has antichain width at most `r`. For the Boolean lattice of subsets
of an `n`-element set, it proves that the exact minimum number of labels is

    ceil(binomial(n, floor(n/2)) / r).

It follows that a self-indexed finite compression exists exactly when

    binomial(n, floor(n/2)) <= r*n.

The paper also proves choice-free infinite obstructions: exact expansion on
every finite subcube; definable Dedekind-infinitude of any hypothetical
infinite example; and an antichain-transfer theorem that rules out every
binary-duplicable set via Forster's finite-to-one strengthening of Cantor's
theorem. Hence the finite classification is complete in ZFC. The remaining ZF
case for width `r >= 2` is stated explicitly as an open conjecture, not as a
solved theorem.

## Build

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

## Verification

    python3 verification.py

The script requires only Python's standard library. It reconstructs and checks
recursive symmetric-chain decompositions through dimension 14, verifies
optimal grouped-chain certificates over a grid of parameters, checks exact
monotonicity through dimension 300, and regenerates the included tables.

## Status

AI-assisted, unrefereed, and not formally verified in Lean or Rocq. Complete
proofs are supplied for the results labeled as proved in the article. Imported
results and the unresolved choiceless boundary are identified explicitly.
Historical priority for the new formulation and intermediate observations has
not been established.
