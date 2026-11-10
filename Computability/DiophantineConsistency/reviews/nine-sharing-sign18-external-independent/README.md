# Independent external audit: sign18 main-root elimination

The independent `check.py` ran with `python3 -I -S -B`, exited 0 and produced
`result.json`, without calling the candidate's builder or checker. Checker
SHA-256: `9e5b1073345db5161d813fcc60a3e0e04c27fc79544b9f2f72fa5e422567b3d6`;
result SHA-256:
`b73b03862676eea06bb916498420d19f8049d1000513cbfa2db840d59e4c96dd`.

The checker reconstructs the root equation and its positive replacement, whose
cancellation follows by distributing `(v9+1)*A`, and checks the replacement
uses only nonnegative constants, variables, ports, addition and multiplication.
It independently reconstructs every retained AST under substitution and
reindexing, checks all nine residuals have syntactic degree at most 47, and
verifies the Na row does not depend on input coordinate zero. A nested
coefficient-list calculation finds `[t^47] Na = -16*beta^28`. Since the
specialized sum-of-squares coefficient at t^94 is a sum of integer squares and
beta is positive, it is at least `256*beta^56`; the external fixed-port degree
is therefore exactly 94. Both gzip/raw hashes, lengths and bit lengths were
checked for all four ports, along with the inherited certificate and proof hashes.

This audit concerns the pinned external transformation and degree argument;
it does not establish Lean/JSON correspondence, a sign18 model bridge, an
iPRA endpoint or nine-variable reduction. Linked certificate and proof contents
are inherited rather than reproved here.
