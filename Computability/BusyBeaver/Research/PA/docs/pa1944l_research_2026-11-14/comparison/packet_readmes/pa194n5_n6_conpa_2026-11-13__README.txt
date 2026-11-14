PA194N5 and PA194N6
==================
Two materially distinct 194-state binary single-tape PA consistency machines.
No machine below 194 states is claimed.

Revision inspected: 1e407ae841e4666f932777fad977ba784ebbcfd5
Date: 13 November 2026, Pacific time.

Read report.pdf or report.tex. The PDF was directly typeset during a runtime
outage; it was not compiled by a TeX engine. The editable report.tex can be
compiled with pdflatex (run twice for the contents). Both state the same
construction, proof, evidence and limitations.

Run:
  node verify.mjs
Requires Node.js 18 or later; no network or third-party package is needed.

Machines:
  machines/pa194n5.tm and pa194n6.tm use states 0..193, start 0, halt 194.
  *.native.tm use the original compiler labels, start 74, halt 254.
  Each line is: state read write direction target.
  Tape alphabet is {0,1}; blank symbol is 0; tape extends both ways.

The verifier reconstructs the source instruction graphs and exact tables,
checks all 32 local fold cases in the simultaneous quotient, checks every
symbolic source outcome for arbitrary registers, and compares the complete
blank startup tape. It also checks exact source-splice relocation.

The mathematical PA proof uses the archived logical calibration, a uniform
constructor-k proof, and the no-push all-store proof compiler. No new Lean/Rocq
kernel theorem or iPRA equivalence is asserted. Reference fragments retain
the dependencies and their original scope; they are not all standalone
compilable documents.

The comparison covers 46 packet deliveries at the pinned revision, with a
fresh exact graph audit of the five incoming archives and their reference
corpora. Duplicate deliveries and rejected tables are distinguished.

New native rows relative to each radix parent:
  old: 164 1 1 R 98
  new: 164 1 1 R 114

Credits: James Chang's PA196 source/runtime, the ProveIt research packets,
and their licenses are retained. New composition, verifier port, and report
were produced for this request.

Optional longer bounded search:
  node neutral_search.mjs reference/pa194.native.tm
Expected baselineContexts=25707, patches=tested=348, hits=[].
This bounded search does not prove that 193 states are impossible.
