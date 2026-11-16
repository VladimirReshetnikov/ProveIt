# Constructive central limit theorems in iPRA

Prepared for Vladimir Reshetnikov, 15 November 2026.

## Start here

- `paper/central_limit_ipra.pdf` - complete 32-page human-readable manuscript.
- `paper/central_limit_ipra.tex` - standalone LaTeX source.
- `THEOREM_LEDGER.md` - statement-by-statement coverage of the requested Wikipedia and MathWorld pages.
- `lean/ROADMAP.md` - concrete route from finite Lean mathematics to an object-language `PRAAx` derivation.

## Main constructive results

For independent centered finite rational laws with total variance `s^2 > 0` and
`rho = sum E|X_j|^3`, the manuscript proves at every rational raw threshold

```text
|P(sum X_j <= q) - Phi(q/s)| <= min(1, 64*rho/s^3).
```

A separate bounded-increment argument proves

```text
|P(sum X_j <= q) - Phi(q/s)| <= min(1, 7*B/s)
```

when every support value satisfies `|X_j| <= B`.  The proof uses exact finite
probability, finite Taylor remainders, an independent-copy damping estimate,
a finite product telescoping identity, and a constructive Esseen smoothing
kernel.  The constants have a purely rational audit.

The manuscript derives effective versions of the iid CLT, uniform CDF
convergence, Lindeberg and Lyapunov theorems, global and local
de Moivre-Laplace, lattice local limits, rational-projection multivariate CLT,
random sums, bounded finite-range dependence, finite-tree martingales,
products/lognormality, and the LLN comparison.  It also gives exact
counterexamples to a universal “sample size 30” rule and to replacing full
independence by pairwise independence.

## Constructive scope

The core theorem is internal to first-order intuitionistic primitive recursive
arithmetic as a theorem schema for fixed primitive-recursive presentations.
Continuous or infinite laws are handled only when their presentations include
explicit primitive-recursive approximation, tail, and continuity moduli.  The
packet does not silently identify qualitative classical existence with an
effective modulus.

The source wording is corrected where necessary: finite variances alone do
not yield a CLT for an arbitrary non-identical triangular array, and a general
sample mean is asymptotically rather than exactly Gaussian.

## Lean status

The files in `lean/` are **uncompiled blueprints**, not a completed Lean
formalization.  No Lean, Lake, or Elan executable was installed in the
preparation environment.  The files contain no `sorry` and introduce no CLT
axiom.  Completion requires:

1. an actual decoder/interval checker `beTest` compiled to `PR 3` syntax;
2. a proof of its defining equations;
3. an explicit `PRAAx` derivation constructing
   `CentralLimitIPRAPlan.InternalProof beTest`;
4. transport through ProveIt's existing `pra_iff_native` theorem.

Standard-model truth or an ambient `Real` theorem does not fill that endpoint.

## Exact validation

Run from the archive root:

```sh
python3 code/finite_clt.py --output code/validation.json
```

The recorded run passes 75 exact integer/Fraction assertions and 39
floating-point regression diagnostics.  Floating Gaussian evaluations are
informational only and are not used as proof oracles.

## PDF build

```sh
./build.sh
```

The script runs the exact validation and uses `latexmk` when available,
falling back to three `pdflatex` passes.  The manuscript requires a standard
TeX installation with AMS, Latin Modern, geometry, microtype, hyperref,
cleveref, longtable, and related common packages.

## Repository baseline

The ProveIt API inspection used commit
`979613af639a0e33b9d17b74af2a5629bb2d749f`, whose `lean-toolchain` pins Lean
`v4.32.0`.  See `provenance/SOURCES.md` for the source inventory and trust
boundary.
