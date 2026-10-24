# Direct certificates and coordinated Diophantine reductions

Research contribution for Vladimir Reshetnikov's ProveIt repository.

**Start with [the article](report/report.pdf).** Its editable main source is
[report/report.tex](report/report.tex). This package contains fully specified
equations, their ordinary mathematical proofs, exact coefficient data,
deterministic generators, independently implemented algebra checkers, and
source provenance.

Repository snapshot: **08200eb10fde2db408c69dffd840d6920a569b1f**.

## Completed results

| Equation | Domain | Unknowns | Exact degree | Additional measurements |
|---|---|---:|---:|---|
| Direct quartic, affine gates eliminated | Nonnegative integers | 3,614 | 4 | 2,954 residuals; 15,996 monomials; coefficient height 127,778,545 |
| Direct quartic, affine gates retained | Nonnegative integers | 6,183 | 4 | 5,523 residuals; 17,430 monomials; coefficient height 1,993 |
| Coordinated projection Q21 | All integers | 21 | 16 | 9 residuals |
| Coordinated projection Q20 | All integers | 20 | 18 | 8 residuals |
| Coordinated projection Q19 | All integers | 19 | 40 | 7 residuals |

Each equation represents existence of a finite ZFC refutation. Composing the
ordinary proofs with the named inherited calibrations yields, in ZFC,
equivalence between its lack of solutions on the stated domain and Con(ZFC).
Neither Con(ZFC) nor absence of solutions is proved.

The direct construction compiles the calibrated C222 numerical calculus.
It does not simulate K215 or use Jones's universal polynomial. Its new
shared CRT certificate cancels local range factorials against one global
factorial scale; heterogeneous bounds, local wire substitution, positive
power specialization, circuit sharing, and nonnegative affine elimination
make the complete polynomial manageable.

The integer construction retains the calibrated large-coefficient tuple
of its inherited machine-based source. It replaces the inspected incoming
21/20/19-variable degrees 20/32/88 by 16/18/40 through explicit integer
polynomial bijections of zero sets. The two Pell-root translations and the
choice to retain Y=a-E and k=eta+zeta prevent degree growth.

These are completed improvements against the inspected snapshot, including
all six incoming archive roots. They are not claims of worldwide priority,
global minimality, or a new variable-count record.

## Exact equations

For every JSON equation file, the single polynomial is the **sum of squares
of the listed residuals**. All listed coordinates are existential variables
over the stated domain. All coefficient symbols in the integer family are
bound to the six supplied fixed integers.

- direct/equation.json: all 2,954 quadratic residuals and the coordinate list.
- direct/expanded_polynomial.json: the complete expanded direct quartic.
- direct/small_height/: both corresponding files for the height-1,993 variant.
- coordinate_family/equations/coordinate21_degree16.json
- coordinate_family/equations/coordinate20_degree18.json
- coordinate_family/equations/coordinate19_degree40.json
- coordinate_family/coefficients/: actual fixed coefficient payloads.

There are no hidden variable exponents, binomial or factorial macros, bounded
quantifiers, or unspecified large constants in these final equations.
The JSON schemas are explained in direct/README.md and the component README.

## Offline verification

Python 3.10 or later and its standard library suffice for the mathematical
artifact checks. From this directory:

    python3 verify.py

This verifies the file manifest and runs the independent checks in ordinary
and optimized Python. It reads the release without changing it.

For a fresh build in temporary staging, followed by exact comparisons:

    python3 verify.py --rebuild

For archive integrity and the complete normal audit:

    python3 verify.py --require-manifest --archive ../ConZFC_Shared_Certificates_2026-10-24.zip

The optional --quick flag runs the independent main audits once. It does not
replace the full audit receipts supplied in the package. See --help for
receipt output and other options.

To rebuild the article with a standard pdfLaTeX installation:

    sh report/build.sh

The exact algebra checks validate coefficient identities, restoration maps,
degrees, graph translation, expanded polynomial data, and finite regression
fixtures. They do not search for a solution of the complete equations.

## Proof boundary

The article supplies ordinary arguments formalizable in ZFC. The direct route
inherits C222-to-ZF refutability and constructible-choice calibration, together
with the Pell-index/power characterization. The integer route inherits the
older native/compiler, signed-Pell, determinant, coefficient, and K215
calibrations of its 25-variable parent. Immediate sources are included and
pinned; the full transitive Lean dependency closure was not rebuilt.

No new end-to-end Lean/Rocq certificate or object-language ZFC proof term is
claimed. Independent exact audits support the literal algebra; they do not
replace the universal proofs or these named dependencies.

## Integration

The package can be imported as a new proposal directory without changing an
existing numbered contribution. It deliberately includes the smaller parent
systems needed to replay the new coordinate reductions; those older points
are labeled as reproductions and are not counted as new results. The source
recipe reconstructs coefficients from finite machine/table data; it does not
execute the machine or query consistency.

Inherited copyright and license notices are preserved under
coordinate_family/upstream/licenses/. New material follows the repository's
MIT No Attribution license. See LICENSE, NOTICE.md, and PROVENANCE.md.
