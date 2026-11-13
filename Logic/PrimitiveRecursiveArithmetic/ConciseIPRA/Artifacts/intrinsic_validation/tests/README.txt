INDEPENDENT VALIDATION SUITE
============================
Run from any working directory:
    python3 tests/verify.py
The script uses only the Python standard library and resolves all files relative
to itself. It does not download anything or import the measured checker as a
trusted library. It extracts the exact kernel AST for isolated in-process tests,
then tests the complete standalone checker in ordinary and optimized (-O) Python.
The reader and final acceptance marker are exercised by the subprocess tests.

The 14 native positive certificate trees and one future-witness capture attack
are attributed in ../reference/FIXTURE_PROVENANCE.json. Original negative cases
are regenerated to avoid storing three copies of each large proof. Seven former
unused-prefix alphabet rejections intentionally become acceptances; these data
have no role in the proved statement. The public goal is always the final item.
JSON true is a documented alias for numerical zero code 1. Public floats remain
rejected, while integral floats can occur in ignored or equality-matched terminal
annotations. NaN/infinity tests exercise Python JSON's optional constant syntax.

The fixed seed generates 12,742 grammar comparisons, 13,120 opener checks,
490 intended positive variants, and 10,866 false or invalid export mutation tests.
The CLI suite performs 232 ordinary/optimized process runs. Finite checks support
the written proof; they do not establish universal soundness by themselves.
Successful mutation of a true statement is not a failure, since malformed or
unused metadata can be harmless. The false export checks are the semantic risk.

The script rewrites verification.json with its runtime details. Exact source
metrics are recorded for CPython 3.12.14 and may vary with ast.unparse on other
Python versions. Its verifier assertions and the supplied receipt are untrusted
audit material, not part of the measured checker.
