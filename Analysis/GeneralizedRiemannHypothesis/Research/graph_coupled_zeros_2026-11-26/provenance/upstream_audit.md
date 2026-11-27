# Selected audit of grh-lean

Pinned revision: `72fead102f663d5c7a407964a13dc0cf9d977207` (25 November 2026). This is a source inspection of the named files, not an independent build, kernel replay, or audit of every transitive dependency. The upstream README reports the machine checks; we do not report them as our own. Retrieved source paths and their original blob hashes are recorded in `source_manifest.json`; the upstream source tree is not redistributed in this packet.

## Exact endpoint and scope

The authoritative public statement file, `grh-compact/src/Statements.lean`, imports only Mathlib. Its `DirichletLNonvanishingRightOfHalf` is
[
\forall N\ge1,\ \forall\chi\pmod N,\ \forall s\in\mathbb C,
\quad \Re s>\tfrac12\ \wedge\ (\chi\ne1\ \vee\ s\ne1)
\Longrightarrow L(s,\chi)\ne0.
]
It covers imprimitive as well as primitive characters. The same file separately states critical-strip zero location. It does not assert GRH for arbitrary Artin, Hecke, or automorphic L-functions.

The five theorems in `grh-compact/src/Main.lean` invoke `New.grh`, `New.zeros_on_line`, and `New.zeta_zeros_on_line`. The first has Mathlib's `RiemannHypothesis` type. The primitive-character theorem is a specialization of the all-character theorem, not an extra assumption.

Sources:
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Statements.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Main.lean

## Proof mechanism actually exposed by the source

The compact guide and `New/Main.lean` describe a covolume argument. Columns are algebraic forms on a definite unitary group, rows are cusp forms on an indefinite unitary group, and the connecting operators are chains of theta lifts. Theorems providing short forms, enough forms, and a lower bound for the size of integral forms bound the same covolume from opposite sides. The main height cancels. The resulting `star_inequality` bounds a weighted nonsplit-prime remainder.

This produces an eventual one-sided estimate
[
R_{d,N}(x)\le x^{-1/2+8\varepsilon}.
]
The square-root saving comes from the number of lifts, chosen on the scale of the square root of x. The conclusion is then analytic: Laplace transforms, control of their poles, a suitable quadratic twist, and Landau's one-sign lemma yield nonvanishing to the right of the critical line. The functional equation supplies the other half of zero location.

Thus it would be inaccurate to describe the upstream proof as a Fourier-positivity or Hankel-moment proof. Such methods may be useful subsequent constructions, but they are not this proof's stated central mechanism.

Sources:
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/GUIDE.md
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Main.lean

## Reusable analytic interface

`PrimeError.lean` defines nonnegative weights supported on the class 1 modulo N and weighted by one minus the quadratic character. Its normalized smoothed error has a meromorphic Laplace transform. At a candidate zero, the transform's residue is a difference of sums of zero multiplicities of the original Dirichlet L-functions and their quadratic twists, divided by the explicit factor phi(N)s(1-s).

`PolarLandau.lean` isolates the abstract theorem: a real measurable function of at most exponential growth, with meromorphic Laplace transform having at most simple poles in the right half-plane, has no nonzero pole residue beyond the exponent of an eventual one-sided upper bound, provided its residues at real candidate poles are nonnegative. This is explicitly identified upstream as a known Landau theorem.

`OneSidedCriterion.lean` supplies a window lemma selecting a second scale and converts prime-error bounds into zero exclusion. `ZeroFreeTwist.lean` supplies a quadratic twist avoiding all zeros of a finite family in a fixed half-strip. The twist step matters: the difference of zero multiplicities in the prime-error residue could otherwise cancel.

Sources:
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/PrimeError.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Analytic/Landau/PolarLandau.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/OneSidedCriterion.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Analytic/QuadraticTwist/ZeroFreeTwist.lean

## Verification boundary and use in the new theorem

The pinned toolchain is Lean 4.35.0 with Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The repository reports dependency only on `propext`, `Classical.choice`, and `Quot.sound`. Its intentionally unproved `Challenge.lean` is a separate comparator specification; the README states it is not imported or built. No `sorry`, `admit`, or `axiom` token occurs in the selected source modules inspected here. This token check is not a logical verification of their dependencies.

For a new graph-coupled entire-function theorem, the actual upstream input is Dirichlet zero location. Determinants suggest a construction, but the new graph determinant identity and collision formula require their own proofs. No Artin or automorphic extension follows merely by replacing the functions in the statement.

README:
https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md

