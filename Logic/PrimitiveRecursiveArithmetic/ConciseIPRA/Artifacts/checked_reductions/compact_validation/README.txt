COMPACT GUARDED CHECKER: OFFLINE VALIDATION
========================================

The measured complete module compact477.py has 273 significant tokens,
305 Python AST nodes, and 477 normalized UTF-8 bytes. control478.py is the
exact incoming zero_test_split control (271/305/478). Only their complete
module sources are charged to these measurements; neither imports any
fixture, verifier, report, or proof database from this package.

Run from any directory:
  python3 /absolute/path/to/compact_validation/verify477.py --audit
  python3 /absolute/path/to/compact_validation/verify477.py --smoke
  python3 /absolute/path/to/compact_validation/verify477.py

The first audits source and fixture hashes plus exact source change and
metrics. The second also runs a small positive, negative, and boundary suite.
The full run reproduces 454 subprocess invocations, including normal/-O
execution, selection probes, and positive-initial-floor attacks. All inputs
are present locally. No network, repository checkout, or source ZIP is used.
The metric target is CPython 3.12.14, as in the pinned repository.

INPUT HEADER AND PROOF CONTRACT

A certificate is one JSON array. Its last item is [A,k], with the public goal
A and initial numerical scope floor k. The canonical adapter uses k=0.
Earlier items are four-field packets consumed from right to left. An unused
prefix is permitted. To run the candidate directly:
  python3 compact477.py < fixtures/compact_context/computation_zero_local.json

A successful execution exits normally and prints exactly ACCEPT and LF.
Exceptions or any different verdict reject.

The theoretical contract is finite exact-integer/list data and a canonical
closed GUARDED Eq/D public goal. The 477-byte module does not independently
validate the entire input alphabet or this public grammar. It must not be
advertised as the fully validating native interface. Those separate checkers
are supplied elsewhere in the parent package.

The initial floor can be omitted from no certificate: the function requires
exactly three arguments, and the root supplies the fixed initial context
[0]. For guarded goals the root's literal numerical zero forces successful
initial floors to be nonpositive. Negative floors add arbitrary numerical
parameters and no assumptions. The closed conclusion remains sound. This
argument does not apply to unrestricted, zero-free native goals.

FILES AND PROVENANCE

compact477_argument.txt explains universal soundness, canonical completeness,
the scope-header condition, and the distinction between theorem equivalence
and exact certificate acceptance.

verification477.json is the retained original 454-invocation receipt. It is
not overwritten by portable reruns. fixture_manifest.json records its hash,
the measured-source hashes, all 67 fixture hashes, exact old ZIP member names
and hashes for the 66 inherited fixtures, and prior expected verdicts in both
Python modes. Each inherited fixture was adapted only by replacing its final
A with [A,0]. The 67th is the inherited empty-auxiliary boundary.

The portable verifier writes verification477_portable_MODE.json. The package
includes the small portable smoke receipt made after materialization. The
full 66-fixture regressions were not needlessly rerun during packaging:
source/fixture hash checks establish that their bytes and adapter are the
ones already exercised in the retained original receipt.

The eager selector rejects an administrative empty-array proof accepted by
the control. Accordingly exact raw-certificate acceptance is NOT claimed.
Canonical nonempty proof traces preserve completeness, while every new
successful trace simulates an old successful trace. All tested positive-floor
acceptances without protected zero are deliberately noncanonical surplus
arity aliases, outside the guarded public grammar. The verifier's
protected_zero flag tests only the header proof's necessary zero condition;
it is explicitly not a substitute public-grammar validator.

No checker here deletes an arithmetic or logical axiom. This composition
improves only the compact normalized-byte coordinate: the 244-token and
267-AST-node records remain unbeaten. Finite regression tests supplement the
written simulation proof; no new Lean/Rocq verification is claimed.
