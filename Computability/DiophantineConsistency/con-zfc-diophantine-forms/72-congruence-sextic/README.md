# Three explicit equations for Diophantine ZFC consistency

**New results: positive-integer equations with 13 variables of degree 28
and 14 variables of degree 24, and an unrestricted-integer equation with
34 variables of degree six.**

This is a research contribution for the ProveIt Diophantine-consistency
collection, compared against commit
9cca523d9f27ad39d52993f4065cbd7e58f8bdd4, including packages 60–67.
The archive contains the paper, full LaTeX source, exact polynomial data,
literal coefficient payloads, regeneration programs, and finite audits.
It is ready for review as a new proposal directory; it does not alter
the existing checked baseline.

## Results and scope

| Equation | Quantifier domain | Unknowns | Exact degree | Other measure |
|---|---|---:|---:|---|
| P13 | Strictly positive integers | 13 | 28 | 98 live arithmetic gates; four residuals |
| P14 | Strictly positive integers | 14 | 24 | 101 live arithmetic gates; five residuals |
| Q34 | All integers | 34 | 6 | Nineteen cubic or quadratic residuals |

For each fixed polynomial, ordinary mathematics formalizable in ZFC,
composed with the explicitly identified native/compiler and finite-refutation
source theorems, proves that **absence of solutions in its stated domain
is equivalent to syntactic Con(ZFC)**. None of the equations decides consistency.

These are three improvements to the inspected catalogue. The first reduces
the degree from 34 to 28 at thirteen positive variables, adding five gates
relative to package 61's 93-gate equation. Retaining the product E=XY
as a fourteenth positive coordinate gives degree 24, compared with the
inspected fourteen-variable degree-26 form. The integer equation reduces
the sextic variable count from 35 to 34. This is not a global simplicity
minimum, a new fewest-variable result, or a claimed major breakthrough.
The cheaper 14-positive degree-26, 15-positive degree-24, 41-integer quartic,
30-integer octic, and high-degree 9-positive/10-integer constructions
remain different tradeoffs.

The new reductions are ordinary mathematical proofs. The exact finite
verifiers do not establish the unbounded native encoding theorem or its
logical calibration. No new end-to-end Lean/Rocq certificate or encoded
object-language BProv derivation is supplied. The repository's separate
object-language obligation is explicitly discussed in the paper and
preserved in provenance/OBJECT_ZFC.md.

## The mathematical contributions

For P13, supply the positive gap C directly and set q=F+alpha+C. Place
the rational expression

    f = f0 + (q-beta-1)/(3 beta)

inside the existing normalized strong Pell norm. Clearing the fixed
denominator gives an integer polynomial. Rational-square-root integrality
then enforces q=beta(3j+1)+1 automatically. The source size bounds are
available before transport signs are recovered. An adaptive main-root
congruence first identifies the exact Pell index and only then recovers
q dividing X. The transport quotient is shown positive at the end.

P14 adds one positive coordinate E and the residual E-X*Y. Its zero set
is the graph of E=X*Y over the P13 zero set. The degree falls to 24,
with 101 gates. This saves one variable at degree 24 relative to the
inspected fifteen-variable, 89-gate construction.

For Q34, two triangular root translations and seven polynomial
restorations reduce the source-64 quartic. The key extra saving keeps
F2=f^2 and replaces

    (fo-c)^2+g-y^2

by the cubic

    F2 o^2-2foc+c^2+g-y^2.

Their difference is exactly o^2(F2-f^2), a multiple of a retained
equation. This gives an exact bijection of complete integer zero sets.
The coefficient of I^4 g^2 in the final polynomial is one, proving
exact degree six after coefficient specialization.

## Reproduction

Python 3 standard library suffices, with no network access:

~~~sh
python3 verify_all.py
python3 -O verify_all.py
~~~

These commands check the delivered polynomial bytes against their
deterministic builders, exact algebraic identities, degrees, nonzero
leading coefficients, variable and operation liveness, source-file hashes,
and byte-for-byte regeneration of both four-integer coefficient tuples.
Independent implementations audit all three equations. The receipt files
state their finite scope.

Build the paper using a standard LaTeX installation:

~~~sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
~~~

The supplied PDF has been compiled and visually inspected. LaTeX packages
are listed in the source preamble. The Makefile exposes the same targets.

## Files

- report.tex and report.pdf: complete exposition, proofs, comparisons,
  provenance, and limits.
- positive13/: literal circuit, proof, two exact symbolic checkers,
  active coefficient binding, exact payloads, source generator, and
  inherited mathematical interfaces.
- positive14/: the product-register lift, full proof, literal 101-gate
  circuit, degree-24 certificates, and independent algebra audit.
- integer34/: nineteen residuals, full 368-term symbolic-port expansion,
  exact restorations, original 41-variable quartic, coefficient recipe
  and payloads, proof, and independent symbolic audit.
- SOURCE_MANIFEST.json: immutable inherited source identities at the
  inspected commit, including current and historical provenance.
- FILE_MANIFEST.json: integrity hashes for the packaged deliverables.
- VERIFICATION.json and VERIFICATION_OPTIMIZED.json: successful finite
  verification receipts.
- DELIVERY_QA.json: clean-extraction and PDF validation results.
- provenance/: comparison sources, explicit formalization boundary,
  literal-machine proof references, and alternative research notes.
- LICENSE and NOTICE.md: license and retained-source attribution.

Both positive equations use the **whole compact source-44 tuple**:
beta=2^590069-1, four ports totaling 295,388 raw bytes.
The integer equation uses the **whole source-34 mixed-parity tuple**:
beta=2^1064921-1, four ports totaling 532,479 raw bytes.
They are different tuples. In both, MF is already shifted by beta;
adding that shift again or substituting only selected ports changes
the polynomial and invalidates its binding.

The 98- and 101-operation conventions count every live binary addition,
subtraction, multiplication, scalar multiplication, and square on
witness expressions. Fixed numeral creation and register reuse are
free. This is an arithmetic-circuit metric, not bit complexity.
