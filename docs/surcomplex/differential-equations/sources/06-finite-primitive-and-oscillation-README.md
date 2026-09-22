# Differential Algebra of Surreal and Surcomplex Numbers
## Primitives, Finite Phases, and Oscillation Obstructions

A 31-page companion article for VladimirReshetnikov/Surreal, dated September 21, 2026.

## Download contents

- `article.tex`: standalone LaTeX source with an embedded bibliography.
- `article.pdf`: compiled article.
- `verify_examples.py`: deterministic exact finite symbolic checks.
- `verification.txt`: actual test output, including environment versions.
- `repository_audit.md`: the pinned snapshot, inspected sources, and coverage rationale.
- `build.sh`: PDF build command, run from any working directory.
- `build_report.txt`: final PDF and LaTeX validation record.
- `requirements.txt`: the version of SymPy used for the recorded check run.

No repository files were changed. No fonts or third-party articles are redistributed.

## The selected gap

The repository's trigonometry report explicitly does not choose a derivation on
No and does not classify solutions of differential equations. This article fixes
the Berarducci–Mantova number derivation (omega' = 1) and develops that missing
interface. It is not another general survey of Hahn analysis or trigonometry.

The audit is tied to commit:

`e260237db9b71da8b74a0c13c8e6355119091100`

The audit was targeted rather than a line-by-line review of every archived report.
See `repository_audit.md` for the exact scope.

## Main results

The article proves that a nonzero solution of

    y' = (a + i b) y,    a,b in No

exists in No[i] exactly when b has a finite surreal primitive. Equivalently, the
image of the logarithmic derivative z -> z'/z is No + i derivative(m), where m is
the class of real infinitesimals. This yields a purely infinite obstruction,
scalar gauge normal forms, and the maximal additive domain No + i O for a
number-derivation-compatible exponential.

It also proves the full homogeneous constant-coefficient classification: only
real characteristic roots contribute exponential-polynomial modes in No[i].
Thus y'' + y = 0 has only the zero surcomplex solution under this derivation.
There is no contradiction with canonical global surcomplex exponentials defined
by different structural requirements, or with ordinary sine and cosine functions.

A forced oscillator nevertheless has a unique exact factorial Hahn-series
solution. The article gives its exact truncation residual, proves set-sized
differential localization, and constructs an oscillatory Picard–Vessiot extension
outside the surcomplex field with no new constants.

## Build

With a LaTeX installation containing the packages listed in the preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Or, on a shell supporting POSIX scripts:

```sh
sh build.sh
```

No BibTeX/Biber run, external figures, or shell escape is needed.

## Run the finite checks

Python 3.10 or later and SymPy are required. The delivered run used Python 3.13.5
and SymPy 1.14.0:

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

The recorded result is **258 checks passed, 0 failed**. Exit status is nonzero on a
failed check or a missing dependency. The code uses exact symbolic arithmetic,
not floating-point approximations or random testing.

## Mathematical status and limitations

The existence and properties of the Berarducci–Mantova derivation are imported
from the cited primary literature. They are not reconstructed or machine-checked
here. Main deductions have proofs in the article; no priority claim or solution
to a named published open problem is asserted.

The finite check suite is not a formalization of surreal numbers, a proof of Hahn
summability, or a verification of the general theorems. It checks the explicitly
listed algebraic formulas and residual identities at finite orders.

The article does not claim a universal symbolic solver, a complete nonlinear or
variable-coefficient differential theory, unrestricted surreal composition, or
surcomplex values for a differential solution of T' = i T. It distinguishes
number derivation from external function differentiation throughout.
