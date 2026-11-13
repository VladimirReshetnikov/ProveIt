# Independent external audit: sign19 Y elimination

The independent `check.py` was run with `python3 -I -S -B`; the outer command
exited 0 and produced the frozen `result.json`. It did not call the candidate's
builder or checker. Its SHA-256 is
`b2f909ddc04e10afa651960b2b3a8a8f6ac5b4415049bfa620bcb1132979809f`;
the result SHA-256 is
`357be89a89cf9473319430668222dc56aef57c2d1b800099b0e301bf5eae1b34`.

The checker independently reconstructed the deleted positive Y gate and every
remaining AST under substitution and coordinate reindexing, verified metadata,
and bounded all ten residuals by syntactic degree 22. A distinct nested
coefficient-list calculation gives the N0 axis coefficient `[t^22] = -beta^14`
in `Z[beta]` with no higher power of t. The square sum has t^44 coefficient
at least beta^28 after fixing integer ports because each contribution is an
integer square. The beta byte string was separately verified positive, so
this gives exact external degree 44 for the retained fixed ports. The gzip and
raw SHA-256, raw lengths and bit lengths were checked for all four ports; the
inherited certificate and proof-file hashes were also checked.

This audit checks the pinned external AST transformation and degree argument.
It does not establish correspondence of these JSON bytes to a Lean expression,
a sign19 natural/model bridge or an iPRA endpoint. It inherits rather than
reproves the mathematical contents of the linked prior certificate and proof.
