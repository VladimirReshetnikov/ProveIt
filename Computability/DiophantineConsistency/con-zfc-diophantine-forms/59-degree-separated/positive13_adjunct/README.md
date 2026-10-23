# Positive thirteen-variable auxiliary quotient

Additional Pareto tradeoff: **13 positive variables, exact degree126,
91 operations** (51 multiplication,24 addition,16 subtraction).
The incoming parent is132/83; this lowers degree at a higher operation cost.
It does not improve the twelve-variable count or claim global minimality.

- `PROOF.md`: full construction and ordered mathematical proof.
- `section.tex`: integration-ready TeX section.
- `thirteen_positive_degree126.json`: full literal polynomial DAG.
- `build.py`, `check.py`, `CHECKS.json`: reproducible builder and checks.
- `PARENT_PIN.json`, `READONLY_PINS.json`: exact source and coefficient pins.
- `upstream/low_degree/`: unchanged late-parent proof and relevant source text.
- `coefficients/`: unchanged whole590069-bit tuple, binding and dependencies.

Run `python3 build.py` followed by `python3 check.py`; install the declared
SymPy dependency if needed. Normal and optimized (`python3 -O`) checker
outputs agree. Scripts supplied by the parent archive are preserved only
as provenance; this build does not execute them.

The coefficient/compiler and K215 syntactic calibration remain explicit
mathematical dependencies. Finite checks do not prove consistency or
replace the unbounded proof. No kernel-checked full ZFC theorem is claimed.
