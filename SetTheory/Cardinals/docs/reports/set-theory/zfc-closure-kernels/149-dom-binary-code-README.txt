Portable whole-tape runtime and blank-start checker

Run with Python 3.10+ (standard library only), without -O:
  python validate_native.py candidate.tm sites.json results

This verifies the complete binary prefix tree, all-natural primitive effects
with arbitrary gap and spare list, and one explicit blank-start trajectory.
It does not by itself prove that the source calculus is equiconsistent with
ZFC; that is a separate source-level theorem in the accompanying report.

Runtime proof rules: literal transitions, natural-length unary scan induction,
and finite-list traversal induction checked against the exact input table.
The 4000 symbolic-step bound only bounds proof search, not machine runtime.
A NOT_PROVED result is not automatically a counterexample. The driver rejects
partial transition tables and non-unique native-to-legacy state mappings.

The runtime modules are copied verbatim from the prior research218 encoding
supplement, k223_merged_runtime_audit/runtime. The driver adapts their generic
proof engine to this source without the obsolete 4581-leaf source pin.
