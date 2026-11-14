BOUNDED REDUCTION SEARCHES

Run from the package root:
  node search/search.cjs machine/pa194haz.native.tm 74 6 256
  node search/search.cjs machine/pa194haz.native.tm 74 8 384

search.cjs implements the three sufficient rules described in the main report:
literal-head local detours, control-dependent +/-2 head translation, and a
neighboring marker-bit representation. Conservative finite-window closures
start with every local tape window at the designated start control. All three
rules return zero reductions in both executed HAZ runs and both HA runs.

HA*_node_radius*.json are exact Node receipts. v8_receipts.json and
earlier_search_results.json record earlier V8 runs on the other machines;
H194 means the supplied N-archive auxiliary MPH, not a new contribution.
auxiliary_local_radius6.json records five more auxiliary graph tests.
auxiliary-status.json gives archived evidence status and the excluded failed
bootstrap. All negative conclusions are bounded sufficient-rule results.

Table start labels:
  primary.native.tm, H194.tm, CSZ.tm, HA.native.tm, HAZ.native.tm: 74
  Q.tm, J.tm, D.tm, M4R.tm, M5.tm, M6.tm: 0
  normalized-fixtures/*.tm: 67 (also recorded in auxiliary receipt)

The function exports allow replaying the local rule independently. The CLI
runs all three rules. grammar_helpers.cjs and earlier_search_results.json
retain the limited AX-tree exploration separately; it is not an exhaustive
search and no reader-score lower bound follows from it.
