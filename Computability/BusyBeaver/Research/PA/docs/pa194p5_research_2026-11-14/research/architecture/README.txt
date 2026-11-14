Architectural investigations and bounded negative results
========================================================

This directory contains research evidence, not a sub-194-state solution.
The delivered machine is elsewhere in the packet. In particular,
runtime193.native.tm is the already published failed-startup runtime core;
it must not be represented as a blank-start consistency machine.

Origin: ProveIt snapshot 4be5c6e3a10292a7466f5d3687e3b39615ff049b,
docs/incoming/pa_sub194_research_2026-11-13.zip,
runtime193/runtime193.native.tm. Its SHA256 is
50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53.

Replays (Python 3 and Node.js; no third-party modules needed):

  python prove_start74_obstruction.py
  python search_marker_helpers.py
  python search_inc74_spares.py
  python search_inc74_spares_left.py
  node audit_scores.mjs

Optional stochastic/timed grammar search:

  node replay_order_search.mjs 22000 71478

The exact theorem
-----------------
start74_permutation_obstruction.tex explains why instruction-router
permutations cannot repair the published 193 runtime with start control 74.
Nine literal prefixes, one per possible scanner target, reach the outward
self-loop 35/0=1R35. No timeout argument is used. The JSON stores complete
finite traces; the Python file reconstructs and checks them from the
hash-pinned table. This is an analytic explanation of an already known
negative permutation result, not a novelty claim or an impossibility
result for arbitrary 193-state constructions.

The bounded helper searches
--------------------------
search_marker_helpers.py examines all 772 choices for scanner 51/0 from
193 existing controls, both writes and both moves. Other rows stay fixed.
It requires exact restoration of the original marking endpoint on all
64 possible radius 4 contexts with fixed bits (-1,0,1)=(1,0,1), within 40
steps and without reading beyond the finite window. Only 0R16 and 0R122
pass. The latter is precisely the published 193 core helper.

search_inc74_spares.py changes 74/0 among the same 772 actions and runs
the actual marked-file increment macro, requiring q40 at the original
file boundary, the first 9 registers correctly incremented, and any valid
nonempty spare tail. It uses 76 concrete register files/selected registers.
All 771 nonoriginal choices fail the first restricted test; the original
1R0 passes all 76. The finite screen has a 3000-step cap, a right bound 50
cells past the original file, and disallows a left-boundary excursion.
search_inc74_spares_left.py repeats with a fixed left context and permits
excursions 8 cells left. The result is unchanged. These are bounded tests,
not proofs that every possible semantic detour is impossible.

At runtime 74/0 detects the erased first 1 of the selected register. It is
not exclusively an exterior append operation. Its arbitrary right
context must therefore be included in any valid replacement proof.

Why one fresh bootstrap control is insufficient in the fixed layout
-----------------------------------------------------------------
For a new control with no incoming transitions, the sole used row is
qnew/0=(w,D,q). If w=0, the remaining computation is blank at existing
control q, up to translation. If w=1, it is exactly the onebit seed with
head +1 or -1 at q. All such cases were already classified in the incoming
archive (193 controls, two append variants, blank and both onebit head
offsets: 1158 cases). They all halt or enter certified rays. Thus
that one-use control adds no untested fixed-layout startup. This does
not exclude changing other rows or physical layouts.

Logical and grammar investigations
----------------------------------
mathematical_findings.md records why deleting the apparent separation
guard is invalid, why Gamma(H) is a prior seed rather than a new logical
idea, and the limits of the head-order experiment.

audit_scores.mjs independently recomputes the principal 194 count and
two Gamma(H) 197 counts, including the 28 local fold cases for each.
data.json includes exact input grammars, source data, reordered seeds,
and the two timed-search receipts. The 21,151 iterations found no admissible
candidate at or below 194. Random seeds and stopping times are recorded;
timing-dependent counts should not be presented as exhaustive coverage.
