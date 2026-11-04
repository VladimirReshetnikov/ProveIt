# Independent audit: conditional N4/R5 scalar growth

PASS as an ordinary-integer conditional inequality argument. Reviewed README `613c39ed6aa24fa43ac8a74e3214518fe1b4e05f9834d5a8cd5e680c38151add`, checker `1c15ba640123601a88c00bda99e6c4919c0e2aa004b8eafd8cca1840f63c91d6`, receipt `723a5cd3d858c50e01fd5a2a988093ccc857fea03f1f736aa6ac00be23def764`, stdout `9ee43301e29a4172527ae3919c7d88f4583ef3f020bc723e7b5b52a50b352597` and empty stderr. Independent unoptimized isolated rerun matched stdout; no flags and -O/-OO reject with exit 1.

For X≥32,Y≥1, P=XY², t=Y(X+1)+1, the stated k and c satisfy kY≥128X³Y⁷ and c≤16t⁴≤16Y⁴(X+2)⁴. Independently expanding 2(32+u)⁴−(34+u)⁴ yields increasing-order coefficients 760816, 104928, 5352, 120, 1, hence (X+2)⁴≤2X⁴. Under the strict premise kY<c, all cancelled factors are positive and 4Y³<X follows strictly. With Y≥q³ and q≥32, H=4Y(X+1)−1>16Y⁴≥16q³Y³>16368qY³; the last coefficient difference is exactly 16q(q²−1024)+16q>0. The argument's strict inequalities and directions are valid.

The packet assumes the polynomial formulas, kY<c, q/X/Y ranges, and, for its second conclusion, Y≥q³; it does not itself bind those facts to a graph or show the weighted projection. It is not a Lean proof or an unconditional N4/R5 exclusion. No Lean was run in this review.
