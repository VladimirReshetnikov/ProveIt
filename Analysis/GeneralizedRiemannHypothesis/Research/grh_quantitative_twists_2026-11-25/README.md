# Beyond Dirichlet GRH: quantitative twisting

Research packet, 25 November 2026.

- `report.pdf`: compiled mathematical research note (11 pages).
- `report.tex`: complete LaTeX source. Build with `pdflatex report.tex` twice.
- `verify.py`: standalone Python 3 exact-arithmetic checks and conductor-exponent calculator; run `python3 verify.py`.
- `verification.txt`: recorded output of those checks.
- `SOURCE_AUDIT.md`: pinned upstream and prior-report references; scope of inspection.
- `LEAN_PORT.md`: concrete, uncompiled Lean formalization plan.
- `SHA256SUMS`: checksums of all deliverable files except itself.

Main result: degree-free polynomial upper bound on the p-power order exponent for a fixed finite packet of constraints, compared with the source's harmonic-sum exponential sufficient bound. The comparison is to the initial Gauss valuation / witness, not the stronger selected-shell Gauss valuation. The new argument gives a positive good fraction in a selected shell and transfers to many characters of the same tame support under the source arithmetic hypotheses. The character order is still exponential in the exponent. No bound on auxiliary prime norms, no proof of a named major open conjecture, no independent Lean replay, and no exhaustive novelty search are claimed.
