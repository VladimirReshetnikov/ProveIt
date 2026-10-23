# A 72-operation relaxed-kernel equation

Main result: 15 positive unknowns, one equation, degree 80, 72 binary
arithmetic operations. This is a degree/operation tradeoff. It is not a
new operation-count record, variable-count record or global minimum.

The relaxed norm is prior art. The included P74 (degree 56, 74 operations)
recovers an already existing historical frontier point; it is not new.
P72 saves one operation against pinned normalized P73, while historical
83/71 and 56/74 points remain incomparable alternatives.

Files:

- report.pdf, report.tex, section.tex: readable mathematical report.
- PROOF.md: full soundness, rank, quotient-restoration and adapter proof.
- p72_relaxed.json, p74_relaxed.json: literal division-free evaluators.
- relaxed15_system61.json: inherited six-equation, 61-operation kernel.
- build_relaxed.py: deterministic generation from the pinned P75 DAG.
- audit_relaxed.py and AUDIT_RESULTS.json: independent stdlib audit.
- COEFFICIENT_BINDING.json and coefficients/: all four complete fixed
  unsigned little-endian integer payloads, with hashes and original binding.
- SOURCE_PINS.json, upstream_verified/: exact proof/source provenance.
- history/: historical Q56, documenting the prior relaxed-norm construction.

Run python3 build_relaxed.py and python3 audit_relaxed.py from this directory.
The audit also works with python3 -O. Compile report.tex twice with pdflatex.

All four fixed ports use the complete Wang943 121-by-8801 tuple,
B=2^1064921. MF is the shifted MF_source. This is the same common tuple
used by the companion wave7 families, and is NOT the smaller
complement-packed wave6/native tuple used in the exploratory draft.
Never mix individual ports from those tuples.
The original binding is retained byte-for-byte as a historical record;
its old relative proof path is inert. The active adapter path is the one
in COEFFICIENT_BINDING.json, pointing into upstream_verified/.

Proof boundary: ordinary mathematics formalizable in ZFC, composed with
the inherited native compiler and literal K215/refutation calibration.
No new end-to-end Lean/Rocq proof is claimed. Normalized P75's same-coordinate
Lean equivalence does not certify this changed relaxed equation. Finite
audits validate arithmetic artifacts, not the unbounded semantic bridge.

No external repository has been modified.
