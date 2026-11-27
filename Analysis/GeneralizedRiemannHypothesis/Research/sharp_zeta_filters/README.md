# Sharp logarithmic support for positive Riemann-zero filters

Research packet, 27 November 2026.

- `report.tex`, `report.pdf`: self-contained mathematical report, including source analysis, the gap-free compression theorem, sharp support asymptotics, a stopband tradeoff, and the prime-ramp application.
- `source_audit.md`: exact source paths and observed blob identifiers, source declarations, and the relation to the merged article.
- `formalization_plan.md`: proof decomposition and precise Lean integration boundary; no compiled formalization is claimed.
- `verification/check.py`: exact rational recurrence checks, floating-point checks of constants, numerical theta transform checks, and illustrative positive atomic quadrature.
- `verification/results.json`, `verification/quadrature_nodes.csv`: output of the check script. These are NOT certified zero data, and do not replace the proof.

## Reproduce

From the extracted directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
python -m pip install -r verification/requirements.txt
python verification/check.py
```

`quadrature_nodes.csv` represents an even atomic measure: mass `pair_mass` is split equally between +node and -node (placed wholly at zero if node=0). The LP illustrates exact-moment constraints only to numerical tolerance. It uses the first 4, 8, and 12 approximate positive ordinates from mpmath, not a rigorous census and not a proof of their simplicity. The theorem permits multiple and clustered zeros.

## Scope

The optimal leading coefficient 1/2 for exact cancellation is proved, and is unconditional for the complex zeros of Xi. The real-ordinate interpretation and stated prime-ramp application use the vendored RH statement. The stopband problem with fixed positive c is bounded, not solved exactly. The construction is existential, not a claim of an efficient algorithm for large B. The full Dirichlet family is not covered by the sharp upper constant. The upstream Lean proof was inspected at its public interface and selected reduction files, not rebuilt or independently kernel-replayed in this session. The new proofs are not Lean-verified. No files were changed in GitHub.
