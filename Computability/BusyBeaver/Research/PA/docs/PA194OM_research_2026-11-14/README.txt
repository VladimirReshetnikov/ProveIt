TWO NEW 194-STATE CONSISTENCY MACHINES
=====================================

Start with report/report.pdf (editable source: report/report.tex).

RESULT
No justified machine with fewer than 194 working states was obtained.
Two fully specified new 194-state binary, one-tape, blank-start designs are
provided: PA194OM and PA194OMF. Their ordinary written iPRA halting equivalence
with the exact revised AX11H is proved with explicit primitive recursive
witnesses. Composing with the included inherited written AX11H calibration
gives nonhalting iff Con(PA) in iPRA. This is not a newly completed end-to-end
Lean or Rocq development.

The constituent operand reassociation, MP reassociation, history selector and
shortcuts are attributed to the supplied research packets. The new work is
their verified interaction in these two complete machines, exact relative
proofs and clocks, the full corpus comparison, and the additional research.

MACHINE CONVENTION
Working states 0..193, initial state 0, separate halt 194. Two-way infinite tape,
blank 0, head 0. Five-column rows: state read write L|R next. Each machine has
388 rows. Native tables use start 74, boundary 84, halt 254; native 194 is working.

PA194OM SHA-256:
a0473681d6d5fb68e5fccfc473f35bc67aa48083d847e349ba3c52865f293629
PA194OMF SHA-256:
6b5f79b2caeb4503c3d12886718caa3a363d241dd17735618fbf95727cc3f088

Both have exactly 3,671 resolved primitive sites, 4,778 source outcomes,
154 changed physical source addresses from AX11H, and 135+66-7=194 controls.
Exact complete blank startups take 58,014 and 58,010 steps, respectively.
Both oracle-free physical replays pass for arbitrary natural registers,
affine padding and arbitrary nonempty finite spare lists.

The positive witness clocks use
  P_AX(k)  =57922+9k^2+685k,
  P_OM(k)  =58014+9k^2+685k,
  P_OMF(k) =58010+9k^2+685k.
For any pair i,j, iPRA proves h_i(t) -> h_j(P_j(t+1)).
There is also a direct physical factor 3 transfer in each direction OM<->OMF.
Here h_i(t) means halted by time t under an absorbing halt convention.

COMPARISON
Pinned ProveIt commit 883da8d55452ea097910ed2509a1eefc833ce292.
106 prior deliveries: 100 filed PA packets plus 6 incoming archives.
104 distinct named 194-state designs in 35 mechanism groups.
The fresh explicit-table scan finds 550 prior 194-control graph classes,
including 548 with a spanning root and 2 disconnected diagnostics. Both new
tables are distinct from all 550 and from each other, even allowing arbitrary
state renaming and root choice, global L/R reflection and read/write bit
exchange, and ignoring terminal-entry write/move actions. Symbol exchange
is used only to strengthen structural novelty, not as a blank 0 simulation.
See comparison/README.txt for exact recognition scope and excluded formats.

REPRODUCE
Python 3.10+; standard library; assertions enabled; no network required.
From this directory:

  python3 -B verify_release.py

This regenerates the tables and oracle-free physical certificates, checks
source closure and clocks, compares all 550 prior graphs, and replays the
recorded exact obstruction and repair counterchecks. It does not repeat
billions of search transitions or kernel-check the inherited PA calibration.

  python3 -B verify_release.py --quick

Quick mode uses retained physical certificates and explicitly reports that
they were not freshly regenerated. Both modes compare all final file hashes
when the archive manifest is present. --output PATH saves a JSON receipt.

Optional longer searches are documented in their research subdirectories;
the C++ programs require a C++17 compiler. Run pdfLaTeX twice from report/
to regenerate the PDF with a normal TeX installation.

RESEARCH LIMITS
The all-start/allocation theorem classifies 70,035,840 choices for one exact
193-control runtime under eleven selector-edge permutations only. All tails
are certified within 94 steps; no complete source frame is reached. This is
not a lower bound for arbitrary 193-state Turing machines.

The broader single-row screen tests 297,607 edits. Its 198 whole-frame hits
represent 163 tables; none validates as the prescribed source implementation.
34,093 bounded bootstrap outcomes remain unresolved. The records distinguish
wrong interfaces, failed symbolic checks, and timeouts.

An arbitrary-consequent gate yields a conservative numerical calculus and
a 3,666-site/4,772-outcome source. Its first literal realization costs 198 states.
Its source binding and arithmetic-box contracts are checked, but no complete
blank-start physical consistency theorem for that candidate is claimed.

LAYOUT
machines/       Complete new tables, source, local folds, physical contracts
construction/   Portable deterministic builder and bound source inputs
verification/   Independent physical checker and release replay receipts
proof/          Written relative proof, binding inspector and receipt
comparison/     Complete ledgers, 550 prior tables and novelty checker
research/       193-control obstruction/search, rotations, grammar search, gate
references/     Exact inherited AX11H calibration and provenance audit
report/         PDF, editable TeX and generated complete transition tables
licenses/       Preserved original licenses

Consult NOTICE.txt and PROVENANCE.json for attribution. All prior source,
machine tables, proofs and optimization ideas remain credited to their
authors. The exact inherited calibration ZIP and its ten current-source
proof-file matches are preserved for review.
