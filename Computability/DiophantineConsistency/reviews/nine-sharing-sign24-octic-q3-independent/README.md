# Independent review of the external sign24 q3 substitution

The independently written `audit.py` checks pinned sign25 and sign24 JSON bytes,
the removed residual `v15 - (beta * (v1 + 1) + 1)^3`, every field and AST of
all 15 remaining rows after substitution and renumbering, the fixed coordinate,
port list and coefficient binding. It verifies each compressed and raw port
hash, the nonzero beta bytes, and the referenced certificate and proof hashes.

For beta and all coordinates nonnegative, the inserted cube is nonnegative;
the removed row then vanishes. Conversely, a zero of the removed row forces
that coordinate to be the cube. These are external algebraic observations, not
a formal model lift or a Lean theorem.

The independent audit computes a syntactic total-degree upper bound of four
for each residual. With coordinates 16 and 17 equal to t and all other
coordinates zero, it calculates the N0 row as the exact univariate polynomial
`-t^4 - 2t^2 - 1`; every other residual has t-degree at most two. Thus the
sum of squares has degree at most eight and coefficient one at t^8, so its
external fixed-port total degree is exactly eight.

The command `python3 -I -S -B audit.py` exited 0; its captured output is
`result.json`. This does not establish JSON-to-Lean semantics, a beta model
representative, an all-model lift/drop, a sign25-to-sign26 bridge, an iPRA
endpoint, or any nine-variable Jones reduction. Port hashes identify bytes;
they do not prove the ports' Lean or PDF interpretation.
