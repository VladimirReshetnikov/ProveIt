# Constructive zeta theory in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 15 November 2026.

## Start here

- `zeta_ipra.pdf`: the developed human-readable mathematical argument, theorem inventory, exact estimates, proof-theoretic interpretation, and formalization plan.
- `paper/zeta_ipra.tex` and `paper/sections/*.tex`: the complete LaTeX sources, without external figures or network dependencies.
- `lean/README.md`: the dependency-ordered path to an actual Lean formalization and the exact trust boundary.
- `code/zeta_certificates.py`: an exact rational enclosure evaluator, including complex arguments and the regularized value at the pole.
- `verification/enclosures.json`: exact rational centers/radii and outward-rounded decimal examples.
- `SHA256SUMS.txt`: integrity hashes for the other files in the archive.

## Mathematical scope

The manuscript lists **33 result families**, many with infinitely many instances. They include:

1. Dirichlet convergence with an explicit primitive recursive modulus and a uniform rotating-block non-Cauchy proof on the entire certified closed half-plane Re(s) <= 1.
2. Euler products, Möbius reciprocal, an Euler logarithm, von Mangoldt logarithmic derivative, five arithmetic Dirichlet series, eta, coprime-tuple and squarefree densities.
3. An entire regular part H(s)=zeta(s)-1/(s-1), constructed by finite Euler–Maclaurin; its derivatives, the unique pole and residue, all Stieltjes constants, and the global Laurent expansion.
4. All nonpositive and positive even integer values; Bernoulli Fourier expansions; zeta'(0), the derivatives at the trivial zeros, and their simplicity.
5. A finite gamma/sine gateway, Gaussian Fourier transform, theta transformation, quantitative propagation of analytic identities, both functional equations, and the entire xi function with its symmetries.
6. An everywhere convergent Euler–Hasse series with a polynomial finite-difference bound and an explicit geometric tail; careful treatment of the exceptional eta quotient points.
7. Mellin, fractional-part, unit-cube and logarithmic unit-square integrals, real monotonicity and log convexity, sums and generating functions of zeta values.
8. An explicit positive rational lower bound on |zeta(1+it)| for 1/A <= |t| <= T, with explicit zero-free disks and corresponding exterior statements.

## What “in iPRA” means here

All analytic notation is interpreted through fixed primitive recursive rational approximation programs and explicit error bounds. For rational inputs the estimates are uniform first-order arithmetic statements. For nonrational real or complex inputs they are theorem schemas in a **fixed certified PR name**, with numerical bounds and regularity/apartness certificates.

The package does not add arbitrary-real quantification, choice, a qualitative identity theorem, or a primitive recursive universal evaluator. Every induction used in the arithmetic reading fixes the final precision first and works with a finite rational invariant. The manuscript explains the coding and error translation, rather than inferring provability merely from computability.

## Formal verification status

**The analytic development is not kernel checked.** The `.lean` files are uncompiled candidates with concrete definitions, finite example proof scripts, and the intended deep-embedding target. No Lean/Lake/Elan executable was available during preparation. No completed iPRA proof certificate is included.

The remaining formal endpoint is a term of `Prf PRAAx [] (residualSentence checker)` for each fixed compiled rational checker (or a sequent under fixed-name hypotheses). The existing `pra_iff_native` bridge only transports a proof after it has been constructed.

The Python software performs exact rational arithmetic. Its mathematical enclosure guarantee uses the proved Euler–Maclaurin remainder and rational ball error propagation. Its finite checks and numerical examples are supporting evidence, not a universal proof or an iPRA proof object.

## Reproduce

From the extracted `zeta_ipra` directory:

```sh
python3 code/check_finite.py
python3 code/zeta_certificates.py --output verification/enclosures.json
python3 code/build_pdf.py
```

The evaluator and finite checks need only Python's standard library. The PDF build requires `pdflatex` and the LaTeX packages listed in the preamble. The build script also supports a Debian-style TeX tree with missing generated format/font-map files by creating task-local build files. Those machine-specific files are not included in the archive.

The optional command `python3 code/crosscheck_optional.py` reproduces the independent 100-digit comparison recorded in `verification/numerical_crosscheck.json`. It requires `mpmath` and is a floating-point diagnostic, not a dependency of the exact evaluator or its proof.

The saved finite run passed 780 exact Euler–Maclaurin polynomial identities (300 with nonzero integral remainder), 359 Bernoulli polynomial identities, 8 known Bernoulli values, 13 exact nonpositive zeta values, 54 rational-ball product-containment instances, and 4 independent-truncation overlap checks. Seven saved example enclosures all have l1 error radius below 2^-30.

## Sources and limitations

The requested Wikipedia and MathWorld pages provide the inventory. NIST DLMF supplies independent formula-normalization references. ProveIt interfaces and selected human-proof dependencies were read at commit `f7e5eac0a94a0e690a22cbeecc5f6cca9270e6df`; the exact paths and Git blob identifiers are in `provenance/sources.json`. No GitHub repository changes were made.

The package does not prove RH, zero-counting or zero-density results, infinitely many critical-line zeros, a Hadamard product, universality, PNT, or irrationality of zeta(3). These omissions are not claims that the known theorems are unprovable in iPRA. Domain certificates are part of each constructive assertion; equality of arbitrary real names is never treated as decidable.
