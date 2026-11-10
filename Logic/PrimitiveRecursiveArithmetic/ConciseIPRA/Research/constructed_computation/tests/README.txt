Reproduce the implementation evidence from the package root:

  python3 tests/verify.py
  python3 tests/convert_reference.py
  python3 tests/audit_constructed.py

The trusted compact checker is code/checker.py. It imports only json.load.
It reads one JSON array from standard input, prints ACCEPT on successful
checking and exits zero. Failures print REJECT and exit nonzero. It works
in default and -O mode and does not depend on assertions for rejection.

code/readable_checker.py implements the exact same protocol in descriptive
names. Neither kernel imports the producer, converter, tests, measurement
code, or baseline programs. All those files are outside the trusted core.

Tests include actual retained-context equation induction, compound case
introduction, transport under Q, arbitrary-term specialization, witness
introduction and elimination, neutral continuations, zero-witness supply,
malformed input, and false-goal controls. Only finite executions are tested.

reference/old_checker.py and reference/old_checker_ast.py are unchanged
source comparators from ipra_generated_assumptions_2026-11-10.zip;
reference/old_folded.py uses the two initialization folds also used in the
new checker. reference/old_witness_cases.json preserves the old fixture set.
The named producer is adapted from that same source archive; its provenance
and the explicit serializer change are recorded in evidence/.
