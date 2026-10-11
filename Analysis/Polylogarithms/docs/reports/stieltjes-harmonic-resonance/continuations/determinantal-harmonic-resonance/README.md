# Determinantal Harmonic Resonance

**Gauss–Vandermonde finite parts, Stieltjes jets, and depth-two polylogarithmic closure**

Research continuation prepared for the ProveIt project, 10 October 2026.

## Reading artifacts

`article.pdf` is the compiled article. `article.tex`, `sections/`, and
`references.tex` are its modular source. `article_standalone.tex` is a
mechanically generated single-file version, convenient for independent
compilation. Edit the modular source and regenerate the standalone copy;
do not maintain the two versions separately.

## Main results

The article proves a discrete Gauss–Vandermonde Gamma product and develops
its first logarithmic resonance. It gives an exact hard-cutoff constant,
a normally convergent subtraction at every fixed Stieltjes order, and
Hurwitz-zeta derivatives and anchored log-Gamma primitives. An independent
rank-one moment argument proves that rational simple-pole weights of
critical decay have cutoff sums affine in a single harmonic number.
Their generating functions have polylogarithmic depth at most two at
arbitrary particle number, and all positive Euler-primitive endpoints
reduce to ordinary zeta values and products of two zeta values.

Explicit results include

    sum(0 <= m < n) (n-m)^2 / [(m+1)_3 (n+1)_3 (n+1)]
      = zeta(3) - pi^2/24 - 3/4.

Here `(x)_k` is the rising factorial. The article contains two- and
three-variable functional generating identities, further double/triple/
quadruple sums, all-order mixed harmonic identities, and a common-translate
cyclotomic extension. Complete human-readable proofs are supplied.

## Replay

The recorded environment uses Python 3.13, SymPy 1.14.0, mpmath 1.3.0,
and LuaLaTeX. The code syntax supports Python 3.10 or later.

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py
python code/make_standalone.py
bash build.sh
```

Run the verification scripts on a working copy when preserving the original
output records: they rewrite their JSON files. After dependency installation,
none of the mathematical scripts needs network access.

The exact suite passes **732 assertions**. The separate numerical suite
passes **85 diagnostics at 100-digit working precision**; its largest
recorded scaled discrepancy is approximately 2.75e-32. Numerical tolerances
vary by test family. Working precision is not an accuracy certificate:
the numerical suite is **not interval-certified**, and its asymptotic tails
are diagnostic. The all-index conclusions rely on the article's proofs,
not extrapolation from these finite checks.

`code/reductions.py` exports exact canonical-family formulas at arbitrary
requested positive rank and nonnegative Euler-primitive order. The general
simple-pole theorem is proved in the article; the convenience API does not
claim to be a parser for every rational weight. The exact suite also checks
selected nonconsecutive pole sets. The common-translate root-filter theorem
is not separately covered by the recorded numerical suite.

## Formula data

`results/exact_formulas.json` stores the cutoff coefficients, normalized
spectral partitions, residues, generating functions, and endpoint values
for ranks 1–4 and primitive orders 0–3. Expressions use SymPy syntax:
`Lk = Li_k(z)` and `Dk = Li_{k,1}(z,1)`. `N` is the maximum cutoff and `u`
is the spectral parameter. Negative powers of `z` in a complete generating
expression cancel at the origin. Do not evaluate individual divergent
pieces at endpoints before combining them.

## Source and integration scope

The selected chapter source anchor is
`87c7db629552afbc2e803001526debe3430a31b0` in
`VladimirReshetnikov/ProveIt`. The repository was changing during retrieval.
The audit inspected selected textual material, not the entire manuscript.
The incoming ZIP directory was inventoried, but its binary archives were
not unpacked or audited. See `integration/SOURCE_AUDIT.md` for the precise
scope and `integration/INTEGRATION.md` for suggested placement.

No substantive false theorem was found in the fully inspected
mixed-Dougall source. The report corrects a possible normalization
extrapolation: the hard-cutoff constant equals the spectral finite part
**minus the derivative of the residue amplitude**. It does not attribute
that mistaken extrapolation to an unobserved source statement.

This package does not resolve S6 or S8, prove period independence or
minimal depth, establish global priority, supply a proof-assistant
formalization, or modify the GitHub repository. It is a research delivery
for separate analytic review and integration.
