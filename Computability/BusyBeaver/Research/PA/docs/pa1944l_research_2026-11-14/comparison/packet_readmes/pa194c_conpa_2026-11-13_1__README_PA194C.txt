PA194C: 194-state separated-diagonal emitter with Combined controller
===================================================================

Primary table: construction/tables/pa194c.tm
Working states 0..193; initial state 0; separate halt 194.
All-zero, two-way infinite tape; head initially at cell zero; alphabet 0,1.
Every working state has one row for each read symbol; all moves are L or R.
Five columns: state, read, write, direction, next-state.

Dense table SHA-256:
d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b

Construction:
134 fixed controls + 67 raw AX readers - 7 compatible folds = 194.
The supplied primary PA194 decoder/folds are unchanged. Six controller rows
install H-only Shift and MP-success-in-H. The resolved 3,649-instruction
source is exactly the previously calibrated PA195C source, checked against
a frozen archive fixture. The ordinary mathematical proof concerns

  PA proves: nonhalting(PA194C, blank tape) <-> Con(PA).

It is not a newly elaborated end-to-end Lean or Rocq endpoint.

Reproduction (Python 3.10+ and standard library, assertions enabled):

  python3 -B construction/build194c.py
  python3 -B independent/verify194c.py
  python3 -B independent/check_commands194c.py

The builder checks the raw and folded tables on all 4,749 universal source
outcomes. The independent checker rederives four generic list-sweep lemmas
from literal transition rows, uses two independent CFG resolvers, checks
all outcomes for arbitrary natural registers and arbitrary nonempty finite
spare lists, and compares the entire blank-start tape after 57,922 steps.
Its recorded evidence is in independent/results194c/. The command checker
checks 188 symbolic command identities with arbitrary opaque stack tails,
both code-zero aliases, axiom selectors and early-halt branches.

PA194CZ is an additional 194-state search seed, not a state reduction:

  python3 -B construction/build194cz.py

Its only further physical edit changes native row 27/read1 to (1,R,21).
Source site 26 changes from jump34 to dec(register6, zero34, positive27).
A common inductive nine-register positivity-mask set of 263,244 pairs
proves register6 is zero at that site. The variant has 4,750 symbolic
outcomes and reaches its exact blank seed after 58,168 steps. Its table
and evidence have the pa194cz prefix. This variant has the construction
checker and invariant certificate, not a separate new independent replay.

The full current proof discussion is report/commands.tex. Unmodified
inherited calibration proofs are in references/. PROVENANCE.json records
the source snapshot, exact archive identities and inherited files.
The construction directory also retains the primary PA194 and its parent
inputs because build194c.py checks those identities before making edits.

No global minimality claim is made. Searches for fewer than 194 states are
separate from this successful materially different 194-state construction.
