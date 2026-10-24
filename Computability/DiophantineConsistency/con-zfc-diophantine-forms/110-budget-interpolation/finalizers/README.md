# Bounded-guard absorption

Main deliverable: **15 unrestricted integers, exact total degree 176,
125 live binary arithmetic operations**, compared with the incoming degree-204,
128-operation fifteen-variable parity equation. It uses the same fixed
coefficient tuple and calibrated seventeen-variable source.

The new idea is not that a radical norm is always nonnegative. It is to subtract
a degree-preserving penalty from a positivity radicand whose *upper* bound has
low degree. Squarehood of that radicand forces every penalized residual to zero.
Thus the norm itself becomes the single final equation.

- `ABSORPTION_PROOF.md`: complete new reduction and inherited semantic boundary.
- `absorbed15_degree176.json`: ordered polynomial specification.
- `absorbed15_degree176_dag.json`: literal division-free arithmetic circuit.
- `ABSORPTION_METRICS.json`: exact degree and arithmetic census.
- `ABSORPTION_CHECKS.json`: independent checks, including a structural degree
  upper bound and finite-difference lower-degree certificate.
- `build_absorption.py`: deterministic reconstruction using retained source tools.
- `check_absorption.py`: independent checker, importing no builder.

Run `python build_absorption.py`, `python check_absorption.py`, and
`python -O check_absorption.py` from any directory. The latter two use explicit
checks, not removable assertions. The finite guard and parity diagnostics are
supplementary; they are not substitutes for the universal proof.

The complete incoming parity package, coefficient payloads, source theorem,
proofs, original licenses and notices are retained unchanged under
`source/con-zfc-parity-norms-2026-10-23/`. Additional extracted incoming sources
under `source/` are research comparisons, not dependencies of this endpoint.

A direct application to the centered-budget seventeen-integer source was also
checked. Its absorption equation would have degree 64 and 111 operations,
compared with that source's degree 48 and 110 operations, so it is dominated
and is not advertised as an endpoint.
