# Independent audit: fixed-payload scalar boundary

PASS for the bounded external arithmetic observation in `research/trace74-fixed-bfs-scalar-boundary/`. We reran the author checker and independently verified all four available parent gzip and decompressed raw coefficient hashes and bit lengths against the pinned candidate JSON metadata, including K0; the audited rank and c dependency cones do not use K0. We independently traversed only the actual JSON dependencies of R, G, Y and c and evaluated those rows using the pinned beta/MC/MF values.

For d=67·8807=590069, `q=beta+1=2^d`, `J=1`, `F=3`, `C=q−3` are positive and give F+C=q. Writing L=MC and H=MF−beta, the checked payload has 0≤L,H<beta, q divisible by 4 and L≡2 mod 4. The graph rows yield `G=(q−1)(q−3)` and `R=q⁴−4q³+3q²+3q+L−3+qH`, with R≡3 mod 4, 3q<R, R≥d and `R+q³+q+1<q⁴`. With the separately selected positive scalar `s=R+1`, eta=zeta=1, the c cone gives Y=q³(R+1), c=2Y+1 and 2R<c.

The cited general upper-window margin is valid independently: for q≥32 and 0≤L,H≤q−2, `q⁴−(R+q³+q+1)=3q³−3q²−4q+2−L−qH ≥ 3q³−4q²−3q+4 > 3q³−4q²−5q+4 > 0`; the final polynomial is positive because `3q³−4q²−5q+4 = q*(q*(3q−4)−5)+4` and q≥32. Our independent checker and output are alongside.

This evaluates selected scalar dependency cones, **not** the full 74 graph output. It does not satisfy or verify the Pell and w-power conditions, prove a fixed-port graph zero or decide the fixed-port guard, establish 74/75 inequivalence, or formally bind the external JSON and payload bytes to the symbolic Lean BFS ports. The first-choice `w=1` is merely a positive placeholder for this scalar audit.

Author checker SHA `66bccdcc129b730f4c46befc53d26e7db9baa320da3afe3f8ee9834ff0296772`; observation SHA `2bc1bc720ff7efc6ecb29ddaf823705fcae730415eeceaaedb0cbcff2e0e843b`. This is external computation; no Lean was run.
