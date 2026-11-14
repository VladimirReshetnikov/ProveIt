# Rejected source-level reduction experiment

No machine with fewer than 194 states was established by this branch.

The main experiment relocated the contradiction test from Shift to the
successful modus-ponens path. This source transformation had already been
studied in the pinned repository at
`Computability/BusyBeaver/Research/PA/docs/pa_consistency_research_2026-11-13_2/command_reduction/`.
It was therefore investigated only as a possible compilation improvement, not
claimed as a novel source design.

The mathematical motivation is sound at the source level: the initial store
contains truth, the axiom and generalization heads cannot first introduce the
contradiction code, and hence successful modus ponens is where contradiction
can first appear. The inherited source proposal tests there and makes Shift
total. Its primitive-site count with the primary PA194 axiom emitter is 3649.

`halt_mp_experiment.py` tried context-sensitive reuse of the existing physical
decoder subtrees. As a calibration, compiling the identity transformation
reproduced the 194-state baseline and passed all 4780 symbolic primitive
contracts. Applying the same reuse strategy to the halt-at-MP source yielded
208 states (20 newly allocated readers), and failed at source site 39 on the
zero branch of a decrement of the top register, after 54 completed contracts.

The failure means that decoder-prefix compatibility alone was insufficient
for reusing the surrounding physical skeleton in this altered source tree.
The generated table is a rejected experiment, not a certified consistency
machine. Its files under `halt_mp/published/` are retained only to make that
negative result inspectable. No proof or state-count claim in the deliverable
should rely on that table.

Other inspected combinations included the incoming SUMS/NS original sum guard
and the radix-5/radix-6 constructor variants. Their additional history folds
both consume native state 41, so the advertised reductions cannot simply be
added: the combined raw table has 203 states and eight directly available
folds, giving 195 rather than 193. A further valid fold was not established in
this branch.

All source references are at ProveIt commit
`317b07268681b44ff352d173a162e2a8c241b2fe`.
