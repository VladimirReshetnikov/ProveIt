# Round-15 selected norm artifacts

Selected certified graphs:
- `integral_centered_paired.json`: 11 unrestricted integer variables, exact degree 464, 119 live binary operations.
- `integral_direct_paired.json`: 11 unrestricted integer variables, exact degree 488, 118 live binary operations.

`DEGREE_PROOF.md` is the complete exact degree and cost proof, including nonzero authentic coefficients. `check_norm.py` checks the full universal identity, coefficient-byte bindings, topology, and exact actual-DAG leading terms. `CHECK.json` and `CHECK_OPTIMIZED.json` are independently run normal/optimized receipts. The mathematical zero-existence proof is `../scalar/PROOF.md`; the independently written complete register-cut and mutation audits are under `../scalar_audit/`.

`build_norm.py` uses only original local arithmetic-DAG code and standard-library modules. `check_norm.py` additionally uses SymPy, already present in the execution environment. It does not execute upstream source files.

The remaining graphs are research comparisons. The two symmetric integral graphs were checked during development but are dominated in cost. The release checker requires only the selected pair. The expanded-cut and rational graphs are exploratory comparison schedules, not selected or asserted to have completed the full semantic and literal verification chain. They should not be promoted merely on the basis of their metric labels.

Every selected graph uses all six fixed payloads in `coefficients/`. They are the complete authentic source34 tuple with already-shifted MF. No port is replaced by a free parameter. All eleven coordinates are unrestricted integers.

The selected graphs include the exact weighted-guard identity Dg81=81Dg. Literal D81,Dg81,P81 replace the unweighted D,Dg,P without changing G or the final polynomial. Rebuild with `python build_norm.py`; verify with `python check_norm.py` and `python -O check_norm.py`.
