Exact current Foundation endpoint comparison
============================================

Current Foundation source pin:
32e1a0956a8622fad067328ca1959729a7634428
as referenced by the ProveIt root gitlink at:
1c9524d8bf2e0a27b9a16ff622359927f536e663

Historical comparator: pa196/vendor/Foundation at that ProveIt snapshot.

Read foundation_endpoint_comparison.tex for the mathematical comparison.
Run python compare_endpoint.py to reproduce the textual equation receipt.
It first verifies all 69 saved files against their pinned Git blob hashes,
then compares 119 equation/template/side-condition blocks and records the
one changed finite axiom separately. Any mismatch exits nonzero. This is
not a Lean proof checker.

Source files are retained under source/ and historical/. manifest.json
and historical_manifest.json give exact git blob identifiers. The JSON
comparison receipt additionally gives raw-source SHA-256 values and each
compared pair of strings. The fetch scripts are original acquisition helpers. They require an existing
ProveIt checkout and Foundation bare cache; they are not used by offline replay.
fetch_historical.py records the original absolute checkout path, which must be
adjusted for a different workspace. fetch.py expects Foundation.git alongside
it; create/fetch that cache at the pinned Foundation revision before using it.
All required source bytes are already included, so normal reproduction needs
neither helper, a checkout, a cache, nor network access.
The two upstream Apache 2.0 license texts are saved as source/LICENSE
and historical/LICENSE and are covered by the pinned-blob check.

Do not identify current/historical PA proof predicates: addEqOfLt changed
from bounded to unbounded existential. The note gives both elementary
derivations between those fixed leaves and the necessary inclusion from
old prenex-Sigma1 induction to the current broad Sigma1 class.

The bare Foundation.git directory is an acquisition cache and is not
needed in the delivered archive. All comparison inputs are in source/.
