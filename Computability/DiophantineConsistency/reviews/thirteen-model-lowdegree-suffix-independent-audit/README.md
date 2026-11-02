# Independent later-source lower-degree suffix audit

The read-only [audit](audit.py) of `e4b90853ef` actually exited 0 in session
15747; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record all eight compiler and direct-dependency rows, anchored source hashes,
both complete 1,149-object parent overlays, the 90 direct companion guards,
matching sibling source/object/log hashes and the successful rerun of the
independent 684-row parent audit. No Lean compilation was rerun. Each side's
six warnings are three unused-variable/section notices and three `push_neg`
deprecations; no log contains an error, `sorry` or `sorryAx`.

The audit checks the exact source statements and reported axiom sets for all
27 named theorems: native, standard and equality-only reference iPRA
equivalences for source expressions 70, 71, 72, 73, 74, 75, 76, 77 and 84.
Every statement uses the current-2011 ports and the positive-shifted source
expression; the right-hand side uses the selected mapped native refutation
predicate, with order erasure in the reference presentation. All 27
reported Lean metatheory axiom sets are `propext`, `Classical.choice`, and
`Quot.sound`.

This suffix checks the compiled source-expression endpoints. It does not
bind those expressions to separate JSON graphs, independently establish
their operation counts or exact degrees, produce PDF displays, or prove a
translated-consistency variant for each. Source-document metrics remain
claims until separately checked; positive-shift syntax and shared
positive-coordinate evaluator size are distinct. The four sources are
anchored to later merge `6f8dd13085`, outside the parent's frozen 342-module
replay. Foundation outer-wrapper, package-transitive/dynamic ancestry and
between-check mutation qualifications remain; compiler limits are sampled
and `lean --deps` has no group/RSS enforcement.
