# Source audit at ProveIt 2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6

## Exact provenance and trust boundary

The vendored `Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh` directory has Git tree `2e133df63d7f4da6b3059c4195324f8e9187ba73`. The GitHub API for `lsernau/grh-lean` at commit `72fead102f663d5c7a407964a13dc0cf9d977207` independently returns that same tree for its `grh` directory. This verifies the complete byte-identical copy using Git's content-addressed tree, not merely the vendor README's assertion. There are 818 files, of which 803 are Lean source files beneath `src` (495 Lib, 306 New, Main and Statements).

I constructed the local import closure of `Main`; it contains all 803 local source modules. All outside imports are Mathlib modules. A nested-comment and string-stripped lexical scan of those 803 files found no code tokens `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, or `implemented_by`. The result and the complete closure are in `source_static_audit.json`. This is a source audit, not a fresh Lean build or independent kernel replay. No installed Lean executable was observed, and I did not attempt the documented one-to-two-hour build.

`Challenge.lean` is outside `src`, contains five intentional `sorry` stubs for Comparator, and is not imported by any source module. `lakefile.toml` default targets are Lib, New, and Main (lines 1-3); the Challenge target is separate (lines 30-32). It must not be mistaken for a gap in Main's import chain.

The package pins Lean v4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (`lakefile.toml` lines 13-16; `lake-manifest.json` lines 6-15). Vendor README lines 23-29 say the package is separate from the ProveIt root build and was not rebuilt on import. Root `lake build` therefore does not verify the vendored GRH theorem.

## Actual theorem scope

`src/Statements.lean` line 1 imports only Mathlib. Its definitions are:

* `RiemannZetaZerosOnLine`, lines 3-4: every zero of the ordinary Mathlib zeta function outside the negative even integers and the conventionally-valued pole s=1 has real part 1/2.
* `DirichletLNonvanishingRightOfHalf`, lines 6-8: for every positive modulus and every complex Dirichlet character, the L-function is nonzero for Re(s)>1/2, except the principal character at s=1.
* `DirichletLZerosOnLine`, lines 10-12: every zero in the open strip 0<Re(s)<1 lies on the half line, including imprimitive characters.
* `PrimitiveDirichletLZerosOnLine`, lines 14-16: the primitive-character specialization.

`src/Main.lean` lines 5, 8, 13, 17, 21 export these statements and Mathlib's `RiemannHypothesis`. `New/Main.lean` lines 28-42 proves the Dirichlet strip conclusion from the half-plane input by the functional equation; lines 47-65 do the zeta case.

The scope is Dirichlet GRH over Q. It does not assert simplicity of zeros or nonvanishing at the central point. It does not itself quantify over all Dedekind, higher-dimensional Artin, Hecke-over-number-fields, or automorphic L-functions. These points are also explicit in Article/sections/src.tex lines 38-66.

## Transferable mechanism

`New/Reduction/MainInequality.lean` lines 7-38 summarizes the core: bound the same logarithmic squared covolume plus twice the index from above and below. The upper bound uses short integral forms and a spanning family; the lower uses the twisted-lattice product formula and torsion specialization. The principal height cancels. The key result `star_inequality` at lines 87-88 is

`D.m * D.totalRemainder <= D.f * D.a * D.logB^5`.

The family has near-full target rank, and the two separate index/covolume budgets are accounted for in the comparison. Torsion selection is therefore genuinely part of the denominator-control mechanism, not merely an analogy attached after the fact.

`New/Reduction/OneSidedBound.lean` line 33 has `Data.primeRemainder_le`, which divides the inequality by the relevant scales to bound a smoothed prime remainder by a main small term plus two remainders at a much larger cutoff. Line 74 gives existence of compatible scales. The prime-number theorem makes the remote-cutoff terms negligible. The theorem at line 200 is `eventually_primeRemainder_le_rpow`, the one-sided bound R_q(y)<=y^(-1/2+epsilon) for admissible q and all sufficiently large real y. `grh` at line 239 invokes the one-sided zero criterion for all auxiliary primes in a prescribed progression, then changes the character's level back. The terminal functional-equation step is elementary relative to this half-plane conclusion.

The auxiliary congruence is q_0 divisible by 18480, d congruent to q_0/2-1 mod q_0. The smoothed coefficients are Lambda(n)(1-(n/d)) on n congruent to 1 mod q_0. The integer 18480 and the large separation exponents are source construction parameters, not restrictions in the final Dirichlet theorem.

## Citation-ready source URLs

* https://github.com/VladimirReshetnikov/ProveIt/blob/2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/README.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Statements.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Main.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean
* https://api.github.com/repos/lsernau/grh-lean/git/trees/72fead102f663d5c7a407964a13dc0cf9d977207

## Article audit scope

The Article README explicitly says that the article merges 120 reports, has 869 results, and is a merge rather than an independent review. I examined src.tex and the relevant spanning, Selmer trace-depth, graph-moment and symplectic-compression portions for possible extensions. I did not verify all article results. Its claims and external certificates should not be described as newly checked in this session.

