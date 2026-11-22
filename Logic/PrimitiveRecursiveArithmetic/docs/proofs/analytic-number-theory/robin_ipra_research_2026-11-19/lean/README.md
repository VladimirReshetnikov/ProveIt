# Checked constructive logical component

Run lean RobinCertificateLogic.lean using Lean 4.32.0.

The file imports only Std and compiles without admitted proofs or custom
axioms. Eight #print axioms commands report no axioms; see
../verification/lean_axiom_audit.txt.

It proves the implications between strict, double-negated, and weak
certificate forms, stability of the negative RH coding, a legitimate
contrapositive rule, conditional assembly from explicitly supplied
certificate transformations, a zero-interval counterexample to generic
weak-to-strict conversion, and bounded Boolean search invariants.

It does not implement the concrete interval or zero checkers and does not
prove the analytic transformations or Robin's theorem. The full object-iPRA
endpoint and mathematical implementation plan are in the report.
