# Selective coprime fusion: eleven unrestricted integers

Complete portable ordinary-arithmetic reduction and literal polynomial circuits.

| File | Integer variables | Exact degree | Binary operations |
|---|---:|---:|---:|
| guard_fused11_aux.json | 11 | 688 | 126 |
| guard_fused11_direct.json | 11 | 728 | 122 |
| fused11_rational.json | 11 | 1632 | 114 |
| fused11_integral.json | 11 | 1892 | 114 |

The last integral variant is retained as a proof/comparison companion; the rational-cleared form dominates it on degree at equal cost. All domains are unrestricted integers. All six fixed ports are actual authenticated numeral payloads with their full finite reconstruction recipe, not parameters. The prior eleven-integer benchmark was2240/206.

Read PROOF.md for both zero-existence directions, exact hypotheses and inherited calibration. section.tex is the report-ready exposition. No global optimum, consistency proof, new Lean/Rocq endpoint or internal object-ZFC certificate is asserted.

Reproduce with Python3 standard library, offline:

    python build.py
    python check.py
    python -O check.py

The checker independently binds every live mathematical register in a free polynomial ring, multiplies all eight radical conjugates and compares all35 coefficients, authenticates all six numeral payloads, verifies topology/liveness/cost, and propagates exact leading monomials through every actual gate (with the explicitly verified centered cancellation cut). It uses no removable assertions. CHECK.json and CHECK_OPTIMIZED.json contain the full receipts.

SOURCE_PINS.json identifies the retained source archive, pinned repository commit and copied proof dependencies. The unbounded centered kernel, main folding, interpolation and native/compiler/refutation theorems remain ordinary mathematical dependencies, distinct from these finite checks.
