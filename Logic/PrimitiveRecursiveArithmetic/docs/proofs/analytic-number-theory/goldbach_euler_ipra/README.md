# Goldbach--Euler theorem in intuitionistic primitive recursive arithmetic

This archive contains:

- `goldbach_euler_ipra.tex` and `goldbach_euler_ipra.pdf`: the complete
  human-readable finitistic proof, explicit convergence modulus, iPRA coding
  audit, and Lean roadmap.
- `lean/GoldbachEulerOutline.lean`: a Mathlib-oriented theorem/lemma skeleton.
  It contains explicit `sorry` proof obligations and is not claimed complete.
- `lean/ConciseIPRABridge.lean`: the final generic transfer step using the
  current ProveIt theorem `pra_iff_native`.
- `FORMALIZATION.md`: staged formalization plan and dependency list.
- `checks/finite_check.py`: standard-library exact arithmetic checks.
- `checks/certificate.json` and `checks/finite_check_report.txt`: generated
  finite audit results.
- `PROVENANCE.md`: sources and repository revision inspected.

## Main result

For the partial sum

```
S_N = sum 1/(p-1),
```

where `p <= N` ranges over distinct perfect powers, the proof establishes in
an iPRA-ready natural-number encoding that

```
0 <= 1 - S_N <= 2^(-k)  whenever  N >= B(k),
B(k) = 2^(2*(k+1)^2).
```

This is a constructive, primitive-recursive modulus of convergence to one.

## Reproduce the finite checks

```bash
python checks/finite_check.py --output-dir checks --canonical-limit 3000
```

## Rebuild the paper

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error goldbach_euler_ipra.tex
```
