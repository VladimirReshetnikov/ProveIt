# Integration guide

Suggested placement: a new uniquely numbered directory under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`.
Choose the number at integration time because the repository is receiving
other reports concurrently. Preserve the exact source and stage identities.

Suggested index description:

> Integral projection after pooled power certificates. Two direct C222 quartics:
> 220 unrestricted integers / 157 quadratic rows / 7,793 collected monomials /
> coefficient height 45,161, and 218 / 155 / 14,410 / 5,023,040. Exact integral
> zero-set bijections from the pinned pooled225 parent; complete printed equations,
> native TeX/PDF, independent finite audits, and a 33,945-rank Macaulay certificate.

Read Section 3 of the report for the general integer-projection arguments and
Section 4 for the complete concrete reduction. Check the balanced equation first:
it improves the immediate parent on all stated varying size measures. The
218-variable companion is a separate coefficient/support tradeoff.

Run both builders and independent verifiers, `verify_rank.py`, and
`export_equations.py`. The printed appendices are parsed back into polynomial
coefficients by the exporter. `SHA256SUMS` records the delivered bytes; rebuild
in a disposable copy when checking release integrity, since TeX produces
auxiliary files and may alter PDF timestamps.

The unmodified original 225-variable archive is included to avoid broken
dependencies caused by repository deduplication of byte-identical inherited
copies. If that archive is deduplicated again, retain its exact blob/SHA-256
locator and a portable way to recover all inherited files.

The result imports the ordinary parent arithmetic and logical calibration.
Keep that boundary explicit. The included selected Lean files are inspection
material, not a newly built formal endpoint or a complete Lean dependency closure.

This submission does not require changing the maintained one-page equation or
its preferred size metric. It adds two concrete direct-family tradeoffs.
