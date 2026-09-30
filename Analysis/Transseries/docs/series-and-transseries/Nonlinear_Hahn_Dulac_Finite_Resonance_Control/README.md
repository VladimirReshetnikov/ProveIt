# Finite Resonance Control of Nonlinear Hahn–Dulac Transseries

**Exact logarithmic slopes, analytic realization, and accumulation thresholds**  
Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

`nonlinear_hahn_dulac.pdf` is the 27-page article. The editable, standalone source is
`nonlinear_hahn_dulac.tex`; its bibliography is embedded. The archive also contains
`verification/verify.py`, the recorded `verification/results.json`, pinned Python
requirements, `build.sh`, and proof, provenance, and build notes.

## Main results

For `(x d/dx - A)y = F(x,y)`, the constant matrix has real spectrum and the
logarithm-free coefficients of F are supported in a well-ordered additive real
monoid Gamma. The monoid need not be locally finite. F has no constant or linear
term of action zero, and the solution has positive actions.

**Exact finite resonance control (Theorems 4.4, 5.1, 5.2).** The optimal bound
`degree(P_gamma) <= theta * gamma` is determined by the actual polynomial blocks
at the finitely many resonant actions. Those blocks depend polynomially on a
finite divisor-closed collection of input coordinates and resonant constants.
The slope sublevel sets are algebraic. The slope itself is not a polynomial
function of parameters.

**Coordinate invariance (Theorem 6.2).** The maximal degree-to-action ratio is
unchanged under logarithm-free local changes of the dependent variables with
invertible constant linear part. A global finite logarithmic degree bound is
not invariant and need not exist for nonlinear equations.

**Universal analytic realization (Theorem 7.1).** Every absolutely convergent
input on the whole monoid has a coefficient-absolutely convergent normalized
solution if and only if nonresonant actions are uniformly separated from the
eigenvalues of A. The proof gives explicit contraction and remainder bounds.
This is a universal criterion, not a necessary condition for every individual
input. The relevant spectrum here is the spectrum of A, not its differences.

**Sharp nonlinear accumulation threshold (Theorem 10.1).** For

```
(D - 2)y = a*x + b*x^2 + c*y^2 + sum_{n>=2} t_n*x^(2-1/n),
```

the slope is 0 when `b+c*a^2=0` and 1/2 otherwise, independently of the entire
accumulation tail. Absolute coefficient convergence is equivalent to
`sum n*abs(t_n) < infinity`. For nonzero `t_n = epsilon/n^p`, with p>1, the
normalized expansion therefore converges absolutely exactly for p>2, even with
nonlinear feedback.

Twelve further research directions are developed in Section 12.

## Scope and novelty

The article supplies conventional mathematical proofs, not a Lean formalization.
It acknowledges the repository's existing linear residue and Hahn–Fuchsian work,
Neumann's lemma, generalized-series fixed points, and the classical Dulac degree
and polynomial-norm methods of Goryuchkina and Gontsov. The proposed additions
are the exact finite nonlinear control, its algebraic and invariant refinements,
and the nonlinear accumulation theorem, together with the stated convergence
extension. The comparison was targeted, not exhaustive; historical priority and
independent peer review are not claimed.

The maximal slope is a supremum over all actions, not a tail limit superior or
an exact analytic radius. A finite divisor certificate is not an algorithm for
discovering divisors in an arbitrary opaque real support. Divergence of the
specified expansion does not exclude other analytic or renormalized solutions.

## Build the article

From this directory, run:

```sh
sh build.sh
```

A standard TeX Live installation with pdflatex and the packages listed in the
preamble is sufficient. Three passes resolve cross-references. No external
bibliography processor, repository checkout, private font files, or network
access is required to build the PDF.

## Reproduce the finite checks

```sh
python -m pip install -r verification/requirements.txt
python verification/verify.py
```

Python 3.10 or newer is required. The recorded environment was Python 3.13.5,
SymPy 1.14.0, and mpmath 1.3.0, with seed 20260929. Run without `-O`; the program
rejects disabled assertions. It uses no network once dependencies are installed.

The successful run records 200 exact block component identities, 393 exact
nonlinear coefficient-component identities, 16 random coupled systems and slope
comparisons, 22 geometric/cascade coefficient comparisons, four finite prefixes
of the accumulating model, and 12 numerical tail-bound illustrations. Categories
overlap and should not be added as independent theorem checks. Numerical
illustrations use 80-digit floating-point arithmetic, not interval arithmetic.
The infinite-support theorems rely on the proofs in the article.

## Repository provenance

Repository: `VladimirReshetnikov/ProveIt`.
Observed snapshot: `3d5973524506411392a911470b5ddc35521568ea`.
Inspection was limited to selected relevant sources and documentation; it was
not a complete audit of the repository or all newly delivered archives.
No repository files were modified. Detailed provenance is in `notes/` and
Appendix B.
