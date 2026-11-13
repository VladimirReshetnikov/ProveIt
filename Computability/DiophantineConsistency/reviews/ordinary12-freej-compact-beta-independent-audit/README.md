# Independent compact first-port audit

The read-only [audit](audit.py) of commit `a114e71252` actually exited 0 in
session 7427. Its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record the result. It checked both committed source and evidence, the paired
source/seed/object chains, 93 project overlay links and BusyBeaver links per
side, direct imports, logs and recorded child exits. Author session 95765's
outer exit 0 is recorded in the packet; the immediate radix-alignment parent
audit was independently rerun and exited 0. Both output objects match, and
both reports list only the Lean metatheory axioms `propext`,
`Classical.choice`, and `Quot.sound`, with no warning or `sorryAx`. No Lean
compile was run for this audit. Resource measurements are sampled, not a
continuous whole-process-tree bound. The inherited manifest-at-read,
README-drift guard, Foundation outer-wrapper and package-transitive/dynamic
ancestry qualifications remain.

The first lemma establishes model facts for the natural numeral
β = 2^590069−1 in an IΣ₁ model, using internal exponentiation. The graph
lemma assumes the **explicit natural equality** `p 0 = 2^590069−1`, in
addition to positive coordinates, internal zero of the free-J graph, and
the port bounds `p 0 > 0`, `p 2 < p 0`, and `p 3 < 2 * p 0`. Under these
assumptions it obtains model `N > 0`, `q = 2^(590069*N)`,
`590069*N ≤ R`, `w = 2^(R−590069*N)`, and `v 5 = q*w`, with q and R
as defined by the graph. Powers and subtraction in the conclusion are
model operations. In particular, this theorem assumes the first-port equality:
it does not connect the actual compact44 payload, fixed full tuple, or checker
to it, nor establish an iPRA proof or the final consistency equivalence.

The retained exploratory record reports attempt 01 exited 1 with `sorryAx`,
attempt 02 exited 0 with a large-exponent warning, and the symbolic third
attempt exited 0 without warnings. It also records that session 35049 and a
separate agent's session 94020 overlapped because of a coordination error;
both exits were observed, and subsequent runs were coordinated. These
observations are distinct from the successful paired replay.
