INDEPENDENT COMPOSITE VALIDATION AND BOUNDED STATE-REDUCTION SCREENS

These files concern two new 196-state composites built by combining the
H-only Shift and MP-result-in-H interpreter changes with the supplied diagonal
and separate-vacuity axiom layouts. No machine below 196 states is established
by these searches. No end-to-end theorem inside PA or a proof-assistant kernel
is claimed here.

Inputs and evidence
-------------------
inputs/*/machine.native.tm and sites.json are the exact new composite tables
and source trees. Native initial control is 74, interpreter root is 84, and
halt is 254; each table has 196 working controls. recorded/*/table.txt is a
dense conjugate with initial 0 and halt 196. recorded/*/receipt.json contains
the complete native/dense control mapping and SHA-256 input identities.

The independent symbolic checker uses the pinned repository's affine
whole-tape representation with arbitrary natural primary-register values,
arbitrary nonempty finite spare lists, and gap at least 48. It proves generic
list sweeps, then checks every source instruction and both decrement outcomes.
It also executes the exact 57,922-step blank startup and compares the whole
finite-support tape to the specified source seed.

Before collecting contexts, a separate pair of ordinal CFG resolvers checks
the source graph, and a finite positive/zero register-mask fixed point is
computed from source site 25 with candidate register 2 and all other logical
registers 0. The mask abstraction is sound because a positive decrement may
yield either zero or positive. It is not exact reachability.

Source-condition five-cell windows include all literal states during symbolic
contracts, all positions in affine unary sweeps, the generic finite-list
interiors using a separate blank-start abstraction, and every startup step.
Unknown run lengths are overapproximated independently. Intersecting these
windows with a radius-six blank-window invariant remains sound. Each window
in an overapproximation need not occur in the actual blank run.

Results
-------
diagonal196: 3,676 source sites; 265,964 source-mask pairs; 4,784 instruction
contracts; 1,113,774 symbolic steps; 2,763 blank-projected five-cell windows
reduced to 2,209 by the source constraints.

separate196: 3,649 source sites; 263,244 source-mask pairs; 4,749 instruction
contracts; 1,105,584 symbolic steps; 2,773 blank-projected five-cell windows
reduced to 2,219 by the source constraints.

No one-helper-row fold survives on either composite. Both composites
also have no two-keeper-row or two-arbitrary-helper-row fold in the stated
five-cell, 16-child-step, single-parent-step simulation template. The exact
counts are retained with the receipts and replay outputs. Failed bounded
screens are not state-count lower bounds.

Two additional searches use a different template. scan_bypass.cpp removes a
noninitial, non-self-loop state by replacing its incoming rows. It matches
two parent steps by a positive child block of at most 64 steps, permits
temporary changes to the predecessor bit, and requires whole-window tape
restoration. Candidate blocks may not touch another independently changed
incoming row. The default replay uses nine-cell windows, refined by the
source-conditioned central five cells. scan_pair_bypass.cpp removes two
controls and checks direct contraction to one child step, following parent
steps through the removed controls for at most 64 steps. Neither screen finds
a reduction. check_bypass.py independently checks all 16 compatible windows
of a synthetic example requiring a temporary predecessor tag; its two parent
steps match four child steps.

The additional scan_stutter_bypass.cpp searches a broader one-control
deletion: parent and child blocks may each take up to 64 steps, and the
parent need not match after exactly two steps. It also permits the deleted
control to have a self-loop. The same whole-window equality and independence
restriction applies. All 195 noninitial controls are considered, with
156,016 transition choices on each composite. No survivor is found.

Mathematical command audit
--------------------------
composite_command_audit.tex proves the changed command contracts uniformly
for both AX stack lengths (9 and 10 entries). It supplies exact Push, Pop,
Discard, axiom selectors, generalization, and proof-compilation words, with
explicit early-halting behavior and the Cantor zero-stack alias. The proof
compiler yields a contradiction word that halts from every incoming store.
The fragment carefully states which inherited logical/tape interfaces are
still required for a PA-internal end-to-end calibration.

check_composite_commands.py supplements that proof with 164 and 188 exact
symbolic cases. check_composite_binding.py resolves the old and new source
graphs independently, checks the 3 retargeted exits and exact 15-instruction
new tail, and replays the two inherited free-algebra emitter audits.
recorded/composite_novelty.json reports the independent corpus comparison:
neither composite is isomorphic, even without an initial-root constraint,
to any of the 401 old literal-table graph classes (90 with 196 controls).

Reproduction
------------
Python 3 and a C++17 compiler named g++ are required. No third-party Python
dependencies are needed. Do not use Python -O, because the inherited symbolic
checker uses assertions as required checks.

  python3 replay.py

This compiles the search engines, checks the positive bypass control, verifies
the manifest and input/context hashes, checks the command algebra and source
binding, and reruns the shorter screens from recorded contexts.

  python3 replay.py --extended

Also reruns the two-arbitrary-helper-row search. Runtime is host dependent.

  python3 replay.py --full

Recomputes both complete symbolic context certificates from the source
programs and literal tables before rerunning all screens. This takes several
minutes. The recomputed receipts must match the recorded deterministic data.

Original sources and licensing
-----------------------------
PROVENANCE.json identifies inherited source files and the pinned repository
commit. Original notices are retained in copied files; LICENSE.JamesChang and
LICENSE.ProveIt are included. New files in this folder implement the described
orchestration and bypass experiments. Binary executables and results/ are
reproducible build outputs and need not be retained in the research archive.
