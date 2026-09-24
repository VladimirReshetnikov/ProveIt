# Classical Complex Theorems over the Quaternions
## Slice-regular and Cauchy–Fueter analogues, with proofs

An expository mathematical paper, dated 20 September 2026.

## Contents of this archive

- `quaternionic_analysis.pdf`: the 27-page paper, with a linked table of contents,
  theorem and equation cross-references, and a bibliography of ten primary sources.
- `quaternionic_analysis.tex`: the complete, editable LaTeX source. The bibliography
  is embedded; no external figures or bibliography database are required.
- `verify_identities.py`: dependency-free exact arithmetic checks of selected
  noncommutative identities and polynomial differential formulas.
- `verification.txt`: the output from running the supplied checking script.
- `README.md`: this file.

## Mathematical scope

The paper develops left slice regularity with right power-series coefficients
on axially symmetric slice domains meeting the real line. Its results include
Cauchy and Taylor formulas, representation and identity principles, maximum and
minimum modulus, Liouville, Schwarz and regular Schwarz–Pick, the quaternionic
fundamental theorem of algebra, spherical multiplicities, the argument principle
and Rouché, qualified open mapping, intrinsic Riemann mapping, real-centered
Laurent and residue theorems, Casorati–Weierstrass, Montel, and Hurwitz.

It separately develops left Cauchy–Fueter regularity on ordinary domains in four
real dimensions: Green and Cauchy–Pompeiu formulas, derivative estimates,
analyticity, harmonicity, mean values, maximum modulus, Liouville, Morera,
removable singularities, and flux residues. The final part proves the Fueter
mapping theorem and constructs an inverse in the simply connected axial setting
by integrating two closed one-forms. Counterexamples identify qualifications
that are essential to the quaternionic statements.

There are 30 theorems, seven propositions, four lemmas, and five corollaries,
each with a proof. Standard scalar complex analysis and elementary real analysis
are prerequisites. This is a synthesis of established mathematics, not a claim
of new priority.

## Building the PDF

Use a current TeX Live or MiKTeX installation with the packages named in the
preamble, including `newtx`, `amsmath`, `amsthm`, `mathtools`, `microtype`,
`geometry`, `hyperref`, and the other standard layout packages.

From this directory:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error quaternionic_analysis.tex
```

Alternatively, run `pdflatex quaternionic_analysis.tex` three times to resolve
the table of contents and cross-references. No shell escape is required.

## Running the supplementary checks

Python 3.9 or newer is sufficient; no third-party packages are needed.

```text
python verify_identities.py
```

The recorded run passed 567 exact checks. The script uses rational quaternion
arithmetic for 60 deterministic test cases, and exact multivariate polynomial
arithmetic for the identities D(Delta(q^n)) = 0 and Delta^2(q^n) = 0,
0 <= n <= 8. It also checks explicit counterexamples and the first few Fueter
images. There are no floating-point tolerance tests.

These finite checks supplement the written proofs. They do not formally verify
the analytic theorems or establish universal statements by sampling.
