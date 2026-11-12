# Five rules for intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 11 November 2026.

## Result

This package simplifies the current canonical successor-seeded presentation to five inference schemes and an Eq/D public formula language. Contexts hold reusable antecedent/consequent clauses. Equality transport uses a single term template. The report proves equivalence with the pinned six-rule calculus, including both formula round trips; numerical translations are identities. Composing with the inherited arithmetic bridge gives whole-domain bi-interpretability and equiconsistency with full first-order iPRA, with actual equality and composite graph `x=y`.

The improvement combines existing mathematical ingredients. It is not a claim of a new arithmetic breakthrough or an absolute minimum. Clause storage, the neutral premise for ordinary assumptions, normalization, syntax validation, and variable scopes are all included in the verifier and its measurements.

## Main files

- `report.pdf`: complete report, full five-rule specification, proofs, interpretations, measurements, limitations, and further research questions.
- `report.tex`: standalone LaTeX source with the full primary checker listing embedded.
- `FORMAT.md`: complete certificate, syntax, and scope specification.
- `code/arity_checker.py`: the complete primary verifier, with no nonstandard dependencies.
- `comparison/arity_current_control.py`: the old six-rule calculus using the same variable representation and shared opener.
- `comparison/canonical_checker.py`: byte-authenticated pinned upstream checker.
- `evidence/`: source provenance, reproducible measurements, and validation results.
- `reference/`: exact attributed upstream mathematical source files supporting the unchanged arithmetic bridge.

## Measurements

All figures concern the entire standalone acceptance module, after docstring removal and CPython 3.12.14 `ast.unparse` normalization plus one LF. Gzip 9 uses timestamp zero and is informational.

| Program | Rules | Tokens | AST nodes | Normalized bytes | Gzip 9 |
|---|---:|---:|---:|---:|---:|
| Shipped canonical checker | 6 | 1338 | 1485 | 4611 | 1205 |
| Matched six-rule control | 6 | 1107 | 1266 | 3820 | 1136 |
| New clausal checker | 5 | 946 | 1072 | 3305 | 1073 |

The matched comparison saves 13.48% of normalized bytes. The 28.32% saving against the shipped checker also includes the change of concrete variable representation. It must not all be attributed to reducing the inference inventory. Historical compressed scalar checkers remain smaller; this package makes no compressed-code frontier claim.

## Run and reproduce

```sh
python3 code/arity_checker.py < examples/reflexivity.json
python3 reproduce.py
python3 reproduce.py --pdf
```

Acceptance prints `ACCEPT` and exits zero. The proof checker uses no assertions for acceptance. Tests exercise ordinary and optimized Python. Python resource limits still apply to sufficiently large valid derivations.

Building the PDF needs a normal TeX Live installation with pdfLaTeX and the packages named in the source. The delivered standalone `report.tex` can also be compiled directly with three pdfLaTeX passes to settle the contents-page numbering. Reference fragments are separate source evidence, not inputs needed to compile that standalone report.

## Provenance and status

The comparison snapshot is ProveIt commit `11be5aabc6b07262046e2553419bc6b05271d178`, under `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`. The inherited ingredients are `canonical_recursors`, the clause presentation in `certified_zero/reference/inherited_choice_basis.tex`, and the `one_context` / `one_sided_transport` developments. Negative rigid parameter labels and shared opening operations also have antecedents in the repository; this package does not claim to originate them.

The new equivalence is a written mathematical proof supported by executable translations and adversarial checks. No new Lean or Rocq verification is claimed. The upstream license for inherited material is retained in `reference/LICENSE-ProveIt.txt`.

## Late source update

While this report was being completed, the repository advanced to `f77135e4aa104b8f60a28e9decd3bded7cb53795` and filed six more packages. The pinned canonical six-rule comparator remained byte-identical. The newly filed `zero_normal/code/zero_six.py` is a different six-rule presentation using initialized I and independent S; it accepts validated general sequents and measures **3095 bytes / 1013 tokens / 1075 AST nodes / 977 gzip bytes**. Its exact source is included as `comparison/latest_zero_six.py`, with the measurements in `evidence/late_source_comparison.json`.

Our five-rule checker has fewer rules and tokens but more bytes than that distinct late presentation. The five-rule uniform clause-use interface is not present in it. The claim remains the explicit calculus simplification and the controlled 3820-to-3305-byte comparison, not a global checker-size minimum.
