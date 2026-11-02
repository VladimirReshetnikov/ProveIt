# Independent 75-row DAG and iPRA binding audit

The read-only [audit](audit.py) of `d384063b1e` actually exited 0 in session
58947; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both three-module source/object/log chains, complete parent overlays,
direct dependencies and companion guards, all recorded child and outer exits,
and a successful rerun of the independent lower-degree parent audit. It also
reruns the independent actual-tuple degree audit. Both sides have matching
objects and logs, and no warnings or `sorryAx`. All ten named axiom reports
per side have the expected Lean metatheory axiom sets. No Lean compile was
rerun for this review.

An independently implemented row parser checks all 75 Lean node definitions
against the pinned JSON in exact order, including all thirteen variable and
four port indices. Port, operator and row-order mutations are rejected. The
compiled `Thirteen75Cuts` theorems bind this node evaluator to the
`ModelThirteenSquares.expressionAt75` source expression and its shifted
model-zero predicate. The compiled client then proves derivability in the
selected native, standard and equality-only reference iPRA presentations for
`Thirteen75Cuts.currentLiteral`, and a standard-iPRA comparison with the
Gödel–Gentzen image of Foundation's selected ZFC consistency sentence.

The graph uses the actual fixed current-2011 tuple. The separately audited
degree calculation establishes exact degree 96 for that tuple; its other
three-port sensitivity bound and nonzero actual-β leading coefficient do not
depend on the stale legacy unit-sphere audit. The 75 operations count the
shared positive-input evaluator; `currentLiteral` applies `positiveShift`
to quantify over unrestricted model naturals, and the unshared shifted
syntax is not claimed to have 75 operations. JSON-to-Lean row checking and
the degree calculation are external finite checks; no formal TeX/PDF
interpretation or global minimum is claimed.

The historical lower-degree parent README was restored to its exact audited
bytes after a later documentation-only edit, so the unchanged pinned parent
audit reran directly. The legacy unit-sphere audit still fails its stale Lean
source pin, as recorded in the separate degree review. Foundation
outer-wrapper and package-transitive/dynamic ancestry qualifications remain;
compiler resource monitoring is sampled, and `lean --deps` has no explicit
group/RSS enforcement.
