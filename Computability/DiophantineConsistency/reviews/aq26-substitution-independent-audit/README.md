# Independent direct-substitution degree audit

[`audit.py`](audit.py) independently reconstructs the pinned 126-row AQ26
graph, recursively decomposes its output into 17 squared residuals, and finds
every residual that directly binds a positive input to a DAG expression,
checking both subtraction orientations and excluding self-dependent values.
It discovers 14 bindings of 13 coordinates. The additional right-oriented
binding `g72 = g71 - qValueVariable`, initially missing from the survey, gives
degree 12 after substitution; the survey was corrected before this audit.

The audit evaluates each substituted DAG with an independent sparse polynomial
implementation, checks the deleted residual vanishes, and independently
recomputes all retained residual degrees. For each case it records a
maximum-degree witness monomial whose coefficient is a nonzero integer times a
power of `beta`; the directly inspected Lean source defines the fixed beta as
`(2^47)^2011 - 1`, which is positive. Consequently the highest homogeneous
part survives the fixed-port specialization, and a real sum of its squares is
nonzero. Positive-variable shifting preserves degree. The complete certificates
are in [receipt.json](receipt.json), SHA-256
`bceb118089fc6c451556c7b689fc849f3e53cad1f25e0bf2428365071803fed8`.

The audit ran at idle I/O / nice 19 and actually exited 0. It rejected three
mutations of the reported results (omitted reverse binding, forged degree,
duplicate binding). Python `-O` and `-OO` each exited 1 at the explicit
fail-closed guard. The first temporary version of the audit failed to parse the
survey JSON because its parent degree checker prints an earlier Python
dictionary; the parser was corrected before the recorded successful run.

This is an independent finite computation on the pinned graph, not a Lean
degree theorem, a positivity or witness-transport proof, an assertion that the
display or graph denotes Con(ZFC), or a search over other rewrites. It does not
establish minimality. Run `python3 audit.py` only after moving aside the
existing receipt; the script refuses to overwrite it.
