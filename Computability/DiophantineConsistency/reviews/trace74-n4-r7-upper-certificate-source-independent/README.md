# Independent N4/R7 shifted upper certificate source review

Source-only mathematical review PASS for SHA `f3f315072c3ea6650d1f38331529d7c947e67d92ece2ad9949c7cd8655cf7fb7`. I independently expanded its exact bivariate polynomial with x=32+u, t=x³+6x²+15x+22+w and z=t(x+1)+2 using arbitrary-precision integer coefficient arithmetic. There are exactly 113 nonzero coefficients; all are strictly positive, minimum 1, and the constant term is 142712638184880673811424625081433. Thus the stated strict inequality holds for u,w≥0 in the intended linearly ordered commutative ring, without an Archimedean assumption.

The theorem is a generic shifted polynomial inequality only; it neither proves the graph supplies those substitutions nor excludes n4/r7. `ring_nf; positivity` elaboration, runtime/memory and package/provider reconciliation remain untested. No Lean was run in this review.
