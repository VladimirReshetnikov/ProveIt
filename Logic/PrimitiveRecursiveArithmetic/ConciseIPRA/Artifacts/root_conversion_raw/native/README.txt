RAW COUNTER-AWARE RECURSION WITH ROOT CONVERSION
================================================

This implementation supports the research proposal described in FORMAT.txt.
It has raw terms, the native Eq/Q/D formulas, and seven rule families:
Hypothesis, Reflexivity, variable substitution, QE, DE, witness-directed DI,
and reversible conversion at the left equation endpoint's root. No redex
address or normalization is used.

The complete new checker is 1029 significant tokens, 1096 AST nodes,
3003 normalized UTF-8 bytes, and 1067 gzip-9 bytes. In the same architecture,
the pinned scalar BH3 checker is 1056 / 1127 / 3089 / 1086. The new normalized
module is measured in full, with no executable code or docstring removed.
It does not beat the repository's compact envelope 244 / 265 / 477.

Run:
  python3 code/verify.py
  python3 code/root_checker.py < tests/transport_symbolic.json

The 29 generated fixtures execute in 58 separate CLI runs, including Python
-O; all expected outcomes are checked. Symbolic transport has multiple
occurrences beneath nested recursor binders; separate tests cover a literal
zero source and a replacement containing older free parameters. The main
symbolic certificate has 4268 bytes and 18 root contractions. Validating
these finite examples is not a formal soundness/completeness proof.

Contents:
  code/root_checker.py       Complete standalone acceptance program.
  code/build_certificates.py Untrusted producer with named, fresh binders.
  code/verify.py             CLI replay and source metrics.
  tests/                    Positive and negative certificate fixtures.
  controls/                 Exact scalar BH3 source for the matched comparison.
  evidence/                 Metrics, hashes, fixture counts, and provenance.
  FORMAT.txt                Exact syntax, rules, scopes, packet, and limitations.

No file imports anything outside this directory except Python's standard
library. The main checker imports only json and sys. The directory can be
copied and the reproduction commands run from any location. The inherited
license is retained in LICENSE-ProveIt.txt.
