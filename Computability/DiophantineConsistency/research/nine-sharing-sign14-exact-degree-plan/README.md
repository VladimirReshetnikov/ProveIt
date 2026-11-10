# Proposed Fin14 exact-degree lower bound

The audited Fin14 symbolic upper client proves total degree at most 124 for
arbitrary integer ports. The following is a proof plan for the matching lower
bound when port 0, called `b` below, is nonzero. It is not a Lean theorem and
does not bind an external file or PDF to a Lean term.

Specialize the dummy coordinate 0 to 1 and each of coordinates 1–14 to `T`
in the staged `Fin 15` seed. Put `s = T + 1`, `q = b*s + 1`,
`Y = s*q^3`, `E = s*q*Y`, and `C = (2*s)*Y+s`. In the shared-node numbering
of `SharingSeed14Degree124`, nodes 13, 18 and 17 specialize to `Y`, `E` and
`C`. Their degrees are 4, 6 and 5, with leading coefficients `b^3`, `b^4`
and `2*b^3`, respectively. The `b ≠ 0` hypothesis suffices over the integers.

The rank node 27 has degree at most 4. Node 25 is `s*C` plus a term of degree
at most 2, so it has degree 6 and leading coefficient `2*b^3`. Thus node 34,
which subtracts rank, has degree 6; node 35 (`s^2 * node34`) has degree 8;
and node 37 (`node35 - C`) has degree 8, also with leading coefficient
`2*b^3`.

The main-root node 38 is `node07 + (E+Y)*C` plus a term of degree at
most 7. Since `E+Y` has degree 6, the product `(E+Y)*C` has degree 11
and leading coefficient `2*b^7`; node07 has degree at most 2. Thus the root
has degree 11. Node 42 is `s*root*(root+2)`, of degree 23 and
leading coefficient `4*b^14`; node 43 is its square, of degree 46 and leading
coefficient `16*b^28`.

In row 03, the expression subtracted from `(T+1)^2` inside the node-43
factor is `(T+1)^2 - node37^2`. Its unique highest term has degree 16.
Consequently row 03 has degree 62 and leading coefficient `64*b^34`. The
other four rows have syntactic degrees at most 46, so its square has the
unique highest degree in the sum-of-squares seed: 124, coefficient
`4096*b^68`. The sign is positive because the inner and outer subtractions
cancel. These are algebraic calculations to formalize, not certified results
of this packet.

A complete Lean lower client must (1) prove the actual staged-node axis
bindings, without relying on external AST identity; (2) prove the polynomial
degree and noncancellation claims, potentially reusing the independently
audited sign17 univariate degree infrastructure; (3) relate the seed axis to
the diagonal specialization of the actual Fin14 expression; and (4) prove
that specialization does not increase total degree. The resulting bound
`124 ≤ totalDegree` under `b ≠ 0`, combined with the audited upper bound and
the existing current-port positivity proof, would yield the symbolic current
exact-degree result. Point-in-time provider surveys and inherited failed-run
ancestry must remain explicit in any guarded union.
