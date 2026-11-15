# The Basel identity in intuitionistic primitive recursive arithmetic

This package gives a complete human-readable finite rational proof of

\[
\sum_{j=1}^{\infty}\frac1{j^2}=\frac{\pi^2}{6}
\]

in the form of a universally quantified primitive recursive arithmetic
inequality, together with a detailed Lean formalization outline.

**Mathematical status:** the paper supplies the full finite argument and
explains how every induction can be quantifier-free.

**Formalization status:** the Lean files are uncompiled specifications and
an outline. This package does not claim a completed Lean proof of the finite
estimate or a completed object-theory iPRA derivation.

## Main result

Let

\[
A_N=\sum_{j=0}^{N-1}\frac{(-1)^j}{2j+1},\qquad
S_n=\sum_{j=1}^{n}\frac1{j^2}.
\]

The paper proves, using only finite rational sums,

\[
n\ge2^r\quad\Longrightarrow\quad
\left|6S_n-16A_{2^r}^2\right|\le\frac{8r+20}{2^r}.
\]

With \(N(k)=2^{2k+7}\) and \(P_k=4A_{N(k)}\), this gives

\[
n\ge N(k)\quad\Longrightarrow\quad |6S_n-P_k^2|\le2^{-k}.
\]

The program \(P_k\) is a fast Cauchy code for the conventional constant
\(\pi\). The paper proves its agreement with independent rational
Riemann sums

\[
Q_M=M\sum_{i=0}^{M-1}\frac1{M^2+i^2}
\]

by the finite inequality

\[
|Q_M-A_N|\le N/M+1/(2N+1).
\]

Thus calculus and real-number induction are unnecessary inside the
arithmetic proof. The ordinary integral
\(\pi=4\int_0^1(1+x^2)^{-1}\,dx\) explains the external meaning of
the same explicit code.

## Files

| Path | Role |
| --- | --- |
| `paper/basel_ipra.tex` | Complete LaTeX paper |
| `paper/basel_ipra.pdf` | Compiled, visually reviewed paper |
| `lean/BaselSpec.lean` | Exact definitions, target statements, and explicit remaining obligations |
| `lean/ObjectTheoryTarget.lean` | ConciseIPRA target and conditional native-core transfer |
| `lean/ROADMAP.md` | Detailed route to a full Lean derivation |
| `code/check_bounds.py` | Exact checks of the square decompositions and error bounds |
| `code/arithmetic_spec.py` | Natural numerator/denominator version of the final inequality |
| `code/integer_spec.py` | Equivalent factorial-denominator, natural-number-only statement |
| `code/check_encodings.py` | Comparison of the two natural encodings |
| `code/check_quadrature.py` | Finite Riemann-sum bridge checks |
| `validation/*.json` | Test results, provenance, and document verification |
| `Makefile` | Rebuilding and checking commands |

## Proof idea

The auxiliary sum

\[
T_N=\sum_{d=1}^{N-1}\frac{(-1)^{d-1}}{d}
       \sum_{j=0}^{d-1}\frac1{2j+1}
\]

is the triangular portion of the finite square \(A_N^2\).
Its complement \(D_N=A_N^2-T_N\) satisfies
\(|D_N|\le H_N/N\), where \(H_N=\sum_{j<N}1/(2j+1)\), by
alternating cancellation in each row.

Grouping the same square by differences of indices gives

\[
A_N^2=O_N-T_N+E_N,\qquad O_N=\sum_{j<N}\frac1{(2j+1)^2}.
\]

Here \(E_N\) is an alternating sum of increasing tail averages and
also satisfies \(|E_N|\le H_N/N\). Therefore

\[
|2A_N^2-O_N|\le2H_N/N.
\]

Odd/even splitting, finite telescoping estimates, and
\(H_{2^r}\le1+r/2\) give the uniform theorem.
Every rearrangement is finite.

The general Gregory-square method is historical. The paper cites
Campbell and Levrie, *On the Basel Problem and the Square of Gregory's
Series*, Mathematics Magazine 97(2) (2024), 181–186,
DOI 10.1080/0025570X.2024.2312093. The finite estimates and
foundational accounting are supplied in full; no originality claim is made.

## The exact first-order sentence

One final encoding uses

\[
F(n)=(2n)!,\qquad B(n)=\sum_{j=1}^{n}(F(n)\mathbin{\mathrm{div}}j)^2,
\]

\[
C(k,n)=\sum_{j<N(k)/2}
\left(F(n)\mathbin{\mathrm{div}}(4j+1)
\mathbin{\dot{-}}F(n)\mathbin{\mathrm{div}}(4j+3)\right).
\]

Subtraction is truncated at zero, and
\(\Delta(x,y)=(x\mathbin{\dot{-}}y)+(y\mathbin{\dot{-}}x)\).
The final sentence is

\[
\forall k\,\forall n\,
\left(N(k)\le n\ \longrightarrow\
2^k\Delta(6B(n),16C(k,n)^2)\le F(n)^2\right).
\]

Under the guard, every divisor divides \(F(n)\).
This is literally a universal arithmetic sentence with a quantifier-free
matrix and primitive recursive functions. The paper supplies the identities
and induction invariants that prove it; primitive recursiveness alone is
not offered as a correctness argument.

## Run the exact checks

Python 3.10 or later and the standard library suffice:

    make check

Or separately:

    python3 code/check_bounds.py --output validation/exact_checks.json
    python3 code/check_quadrature.py --output validation/quadrature_checks.json
    python3 code/check_encodings.py --output validation/encoding_checks.json

Evaluate particular natural-number instances:

    python3 code/arithmetic_spec.py --k 1 --n 519
    python3 code/integer_spec.py --k 1 --n 519

These are instance evaluations, not formal proof checking. Finite testing
does not establish the universal theorem. Default tests finish within
seconds on the authoring system; larger parameters can create very large
unreduced fractions.

## Rebuild the PDF

On a normal TeX Live installation with pdfLaTeX and the packages named
in the source:

    make pdf

The authoring system had TeX binaries and sources but no generated
pdfLaTeX format or default font map. A local format and explicit Latin
Modern/AMS maps were used to compile this exact source. That environment
repair is not needed on a conventional full TeX installation.

## Lean environment and remaining work

The inspected repository is:

    VladimirReshetnikov/ProveIt
    b03925cccc76d55b9dc2a00864a5e0544b64aa7f
    leanprover/lean4:v4.32.0

`BaselSpec.lean` uses Lean core arithmetic.
`ObjectTheoryTarget.lean` needs that file and the existing ConciseIPRA
modules on its search path.

Read `lean/ROADMAP.md` before implementing it. The missing work is:

1. Explicit `PR 2` compilation and representation proofs.
2. Internal arithmetic lemmas and the finite-sum identities.
3. The quantifier-free induction derivations of the bounds.
4. An inhabitant of
   `([] : List (Fm PTm 0)) ⊢[PRAAx] baselFormula compiled`.

The existing `pra_iff_native` theorem then transfers the proof to the
concise native calculus. A theorem about Lean's ordinary real numbers
would not establish this object-theory claim.

No `sorry` or `axiom` declaration is supplied. Outstanding obligations
are explicitly uninhabited structures or inputs to conditional theorems.
This exposes the unfinished boundary; it does not turn the assumptions
into proved lemmas. The files have not been compiled.

The remote repository has not been modified.
