# Independent 84-row DAG and iPRA binding audit

The read-only [audit](audit.py) of `8bfd8dee9a` actually exited 0 in session
86303; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both three-module source/object/log chains, complete parent overlays,
direct dependencies and companion guards, all recorded child and outer exits,
and a successful rerun of the independent lower-degree parent audit. It also
reruns the independent actual-tuple degree audit. Both sides have matching
objects and logs, and no warnings or `sorryAx`. All ten named axiom reports
per side have the expected Lean metatheory axiom sets. No Lean compile was
rerun for this review.

An independently implemented row parser checks all 84 Lean node definitions
against the pinned JSON in exact order, including all thirteen variable and
four port indices. Port, operator and row-order mutations are rejected. The
compiled `Thirteen84Cuts` theorems bind this node evaluator to
`ModelThirteenSquares.expressionAt84` and its shifted model-zero predicate.
The client proves derivability for `Thirteen84Cuts.currentLiteral` in the
selected native, standard and equality-only reference iPRA presentations,
and a standard-iPRA comparison with the Gödel–Gentzen image of Foundation's
selected ZFC consistency sentence.

The graph uses the actual fixed current-2011 tuple. The separately audited
fixed-tuple calculation establishes exact degree 92. The 84 operations count
the shared positive-input evaluator; `currentLiteral` applies `positiveShift`
to quantify over unrestricted model naturals, and the unshared shifted syntax
is not claimed to have 84 operations. JSON-to-Lean row checking and the degree
calculation are external finite checks; no formal TeX/PDF interpretation or
global minimum is claimed.

Foundation outer-wrapper and package-transitive/dynamic ancestry
qualifications remain. Compiler resource monitoring is sampled; `lean --deps`
has no explicit group/RSS enforcement. The source packet was compiled over
the independently audited later-source lower-degree provider.
