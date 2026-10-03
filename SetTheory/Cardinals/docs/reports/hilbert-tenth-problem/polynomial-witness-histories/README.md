# Unique Histories from Linear Equations

**A canonical cellular-computability compiler over N[X,Y]**  
Research report prepared for Vladimir Reshetnikov, 2 October 2026.

## Main result

For a deterministic radius-one cellular automaton with `s` symbols, a quiescent
blank, and a nonblank accepting alphabet, the complete compiler uses
`s^3 + s + 5` polynomial unknowns. Its direct symbol-marginal form has
`3s + 3` affine-linear equations. Exact feature reductions give
**`3 ceil(log2 s) + 6` equations with unit coefficients**, or
**nine equations with coefficient magnitude at most `s - 1`** for `s >= 2`.
All forms have exactly the same complete natural-polynomial solution tuples.
The matrix is independent of the input word, its length, and the running time.
All its entries have at most two monomials and coordinate total degree at
most three; the unit-coefficient bound applies to the symbol and binary forms.

There is a solution exactly when the first accepting configuration has exactly
one accepting cell. In that case the **entire polynomial witness is unique**
and all its coefficients are zero or one. A one-head Turing-machine simulation
supplies a fixed universal instance family. The time and support are unbounded;
this is not fixed-arity ordinary integer Diophantine representation.

The report proves the full normal form, a same-tuple marginal projection saving
`(s-1)^2` equations, further injective-feature compression, exact degree/support formulas, a degree-bound obstruction,
a parsimonious nondeterministic extension, and a single quadratic equation over
the same polynomial semiring.

## Contents

| File | Purpose |
| --- | --- |
| `unique_polynomial_histories.pdf` | The compiled research article, with proofs, example, bibliography, and eight research directions. |
| `unique_polynomial_histories.tex` | Self-contained LaTeX source, including the diagram and bibliography. |
| `code/polynomial_histories.py` | Exact sparse-polynomial arithmetic, generic deterministic CA compiler, pair, symbol, and feature formulations, witness construction, and checking. |
| `code/verification.py` | Exhaustive finite, seeded multistate, adversarial, matrix-invariance, and input-validation tests. |
| `code/export_quadratic.py` | Exact expansion and evaluation of the complete worked sum-of-squares polynomial. |
| `code/feature_verification.py` | Binary and weighted feature checks; exports both feature systems and their expanded quadratics. |
| `results/verification_results.json` | Recorded results of all main tests. |
| `results/example_system.json` | Every variable and coefficient of the complete four-symbol worked system. |
| `results/example_certificate.json` | The full accepting witness and its five configuration rows. |
| `results/example_quadratic.json` | Expanded quadratic, with 2,098 unknown monomials / 5,082 fully expanded terms. |
| `results/quadratic_results.json` | Expanded-polynomial statistics and exact evaluation-check count. |
| `results/feature_results.json` | Feature-test counts, invariance checks, mutation checks, and expansion statistics. |
| `results/example_binary_system.json` and `example_weighted_system.json` | Complete 12-row binary and 9-row weighted systems on the same 73 unknowns. |
| `results/example_binary_quadratic.json` and `example_weighted_quadratic.json` | Expanded feature quadratics; each has 2,704 unknown monomials / 12,364 fully expanded terms, with different coefficients. |
| `SHA256SUMS.txt` | SHA-256 checksums of the delivered files, excluding this checksum file itself. |

## Reproduce the checks

Python 3.10 or later is sufficient. There are **no third-party Python
dependencies**. Run these commands from the extracted package directory:

```text
python code/verification.py
python code/export_quadratic.py
python code/feature_verification.py
```

The scripts use arbitrary-precision integer arithmetic and coefficientwise
polynomial equality. They rewrite the corresponding result JSON files. Elapsed
time in the verification report varies by machine; all other recorded test
counts are deterministic. The main multistate test uses seed `20261002`;
the feature test uses the arbitrary integer seed `20261003`.

The recorded main run checked 59,049 candidate clock flows; 19,200 binary
rule/input/horizon cases; 840 multistate cases; 16,384 independently enumerated
tile assignments (also comparing the pair and marginal systems); and 373
mutations or wrong horizons for the worked example. The quadratic exporter
performed eight exact evaluation comparisons. The feature suite checked both
feature forms on 7,168 binary and 288 multistate cases, rejected all 367
worked-witness mutations per form, and checked both full expanded quadratics.
All assertions passed. Fewer equations need not mean a smaller expanded
quadratic: both feature examples have more expanded terms than the symbol form.

## Minimal API example

From the `code` directory:

```python
from polynomial_histories import (
    compile_system, compile_feature_system, example_ca, witness_for_horizon,
)

system = compile_system(example_ca(), (1, 0, 0, 0, 2))
witness, history = witness_for_horizon(system, 4)
assert system.residuals(witness) == {}
assert len(system.variables) == 73
assert len(system.equations) == 15

# An external horizon is used only to construct a candidate, not by the system.
wrong_witness, _ = witness_for_horizon(system, 5)
assert system.residuals(wrong_witness) != {}

# The unoptimized pair formulation has the same complete natural zero set.
pair_system = compile_system(example_ca(), (1, 0, 0, 0, 2), horizontal="pair")
assert len(pair_system.equations) == 24
assert pair_system.residuals(witness) == {}

# Further same-tuple compression: two bits per symbol or one integer feature.
binary_codes = tuple(((a >> 0) & 1, (a >> 1) & 1) for a in range(4))
weighted_codes = tuple((a,) for a in range(4))
binary_system = compile_feature_system(example_ca(), (1, 0, 0, 0, 2), features=binary_codes)
weighted_system = compile_feature_system(example_ca(), (1, 0, 0, 0, 2), features=weighted_codes)
assert len(binary_system.equations) == 12
assert len(weighted_system.equations) == 9
assert binary_system.residuals(witness) == {}
assert weighted_system.residuals(witness) == {}
```

In JSON, a coordinate polynomial is represented by triples `[i, j, c]`, meaning
`c * X**i * Y**j`. System rows have the form
`constant + sum(coefficients[name] * unknown[name]) = 0`.
Unknown values must be finite polynomials with nonnegative integer coefficients.
Matrix entries and residuals may have signed coefficients.

An expanded quadratic term records a list of zero, one, or two unknown names
and a coordinate-polynomial coefficient. An empty list denotes a constant term.
Products of coordinate polynomials use ordinary commutative multiplication.

## Compile the article

Use a LaTeX installation containing the standard packages named in the preamble,
including `newtxtext`, `newtxmath`, `mathtools`, `amsthm`, `tikz`, `tcolorbox`,
`microtype`, and `hyperref`. Run twice:

```text
pdflatex -interaction=nonstopmode -halt-on-error unique_polynomial_histories.tex
pdflatex -interaction=nonstopmode -halt-on-error unique_polynomial_histories.tex
```

The source is self-contained; no images, bibliography databases, font files,
repository checkout, or network access are needed beyond an installed TeX
package environment. The delivered PDF was rendered and visually inspected.

## Scope and trust boundary

This is an unrefereed research manuscript with complete written proofs and
finite computational validation. It is not a Lean/Rocq formalization. No
particular numerical universal machine table is instantiated in the code;
the universal result uses the explicit machine-to-cellular simulation proved
in the article. The nondeterministic extension is proved but not implemented.

Undecidability of polynomial-semiring linear systems is older work, already
known in one indeterminate. No priority claim is made for the elementary clock
idea, and priority for this precise combined single-fold/Boolean/fixed-matrix
normal form has not been established. The report distinguishes its results
from ordinary finite-fold and single-fold Diophantine questions.

The repository comparison records the starting snapshot
`e58b724c25bd34533b7a5834cfcbe873dfa01288`. It does not claim an audit of every
repository theorem or improve the separate 75/87 arithmetic-operation bounds.
No external paper PDFs or font files are redistributed in this package.
