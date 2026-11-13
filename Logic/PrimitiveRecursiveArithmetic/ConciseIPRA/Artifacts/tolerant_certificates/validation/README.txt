FINITE VERIFICATION BUNDLE

Run from any directory:
    python3 /path/to/validation/test_harness.py

The harness needs only the Python standard library. The recorded run used
CPython 3.12.14, matching the source-metric convention of the incumbent corpus.
It takes approximately 10 seconds in the environment used for this run.

CONTENTS

checkers/tolerant_total.py is the exact measured candidate, unchanged by the
harness. sources.json pins its SHA-256 and the two attributed upstream
controls. Their upstream license is checkers/LICENSE-ProveIt.txt.

fixtures/ contains 31 exact inherited inputs: 13 positive canonical proof
fixtures, 8 proof/scope/capture/false-goal attacks, and 10 invalid outer inputs.
The largest fixture is approximately 100 KB. cases.json preserves each source
path, content hash and expected result. The inputs exercise computation at
zero/successor, retained hypotheses, equation transport, closure elimination,
existential opening, cases, and actual use of an induction hypothesis.

evidence/verification.json is the complete summary and per-process receipt.
evidence/boundary_cases.json records the additionally generated boundary inputs.
evidence/adversarial_trials.jsonl records every bounded search trial, including
its source fixture/mutation recipe or generated pool indices, input hash,
outcome and instrumented call count. The deterministic generator and pool
are in test_harness.py, so all 44,416 trials can be reproduced exactly.

RECORDED RESULTS

Candidate: 315 significant tokens / 361 AST nodes / 603 normalized UTF-8 bytes.
Whole standalone module, normalized by ast.unparse plus one LF; reader and
ACCEPT output included. SHA-256:
cad0fc4bcb549ce9f5df24c2c994614ff5fd24567532c740bde9272329379181

388 unchanged-source CLI executions passed their stated expectations, both
normally and with -O. The 31 shared fixtures were run under the candidate and
both controls. All 13 positive canonical fixtures were additionally accepted
after replacing every integer with its exactly represented float, and after
replacing every zero with False. These inherited fixtures have no scalar 1,
so an explicit paired neutral-major step separately checks actual 1 and True.

44,416 bounded adversarial trials targeted the exact false public goal [0,[0]]:
9,416 systematic single-subtree mutations, 20,000 multiple mutations, and
15,000 new short stacks. All 44,416 rejected; no trial exhausted its 2,000-call
budget or Python recursion limit. No accepted false goal was found.

The unchanged-source CLI tests include active NaN/Infinity neutral majors
before a real computation proof, rejecting the same neutral steps when they
are the only alleged proof of the false goal. They also include empty and
nonempty strings, null, objects, finite fractions, numerical aliases, and unread
noninteger prefixes. The candidate deliberately accepts some sound inputs
which the alphabet-validating controls reject.

REPORT FORMAT

The reports themselves use standard JSON. Actual NaN/Infinity test values are
represented there by an object such as {"python_json_number":"NaN"}.
The test generator serializes the real float with the extra NaN/Infinity
literal accepted by Python's json reader. These literals are not standard
JSON number syntax. The full adversarial JSONL log uses pool indices and
input hashes, so it contains no nonstandard numeric literals.

LIMITS

This is finite implementation verification, not a proof of universal
soundness, termination, completeness, or bi-interpretability. In-memory
instrumentation is used only to bound the adversarial search and is checked
on all 13 positive fixtures. It never edits the measured candidate. Every CLI
test executes the original copied source in an isolated process. The
candidate and the controls intentionally have different raw acceptance
languages; equality of those languages is not claimed.
