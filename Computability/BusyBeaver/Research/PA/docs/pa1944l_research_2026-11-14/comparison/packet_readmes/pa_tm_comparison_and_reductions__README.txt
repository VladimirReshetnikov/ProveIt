PA CONSISTENCY TURING MACHINES: COMPARISON AND NEW REWRITES
Research snapshot: 13 November 2026

Read report.pdf for the mathematical argument, exact changes, comparison,
and verification boundaries. report.tex and all of its input files are included.

CURRENT RESULT
  No machine with fewer than 196 working states is established in this package.
  Two new, explicit 196-state layouts pass complete symbolic instruction-frame
  checks and exact blank startup checks. A separate logical simplification
  reduces the axiom emitter from 201 to 199 macro tokens and the complete
  source from 3812 to 3773 primitive instructions. Its shortest fully checked
  compilation here has 198 states. An explicit 67-rule grammar and two further
  grammar witnesses reusing an existing reader are also included. A grammar's
  rule count is not a physical state count.

  The original PA196 development exports PA |- N -> Con(PA), where N is
  literal blank-tape nonhalting, along with its stated external nonhalting and
  independence results. This package does not export a new Lean theorem of the
  full internal biconditional. See the report for the distinction between
  mathematical proof translations, executable checks, and formalized theorems.

CONTENTS
  report.pdf, report.tex, and the accompanying .tex sections
      Main report, proofs, limitations, and pinned primary references.

  comparison/
      Independent source/tree/control-flow and literal-table comparison.
      Twenty-seven accepted U208 presentations fall into twenty rooted
      isomorphism classes: two original classes and eighteen later helper
      variants. All eighteen local simulation certificates are rechecked.
      Includes PA209, PA196 and the incoming alternative196, for thirty
      reference tables, plus exact startup checks, manifests,
      archive inventory, relevant source files, and original notices.

  rotated196/
      Two new complete 196-state binary machines. Each has a native table,
      a dense table with working states 0,...,195 and halt label 196, a source
      program and site listing, and portable full-frame/startup verification.
      Native labels have start 74, root 84 and halt 254. Dense labels have
      start 0, root 75 and halt 196. Do not mix the two numbering conventions.

  grammar67/
      Independent, standard-library checker for the equivalent 199-token word
      and the explicit MILP grammar witness. Formula constructors, head order,
      implication exchanges, source hashes, and solver limitations are recorded.
      Checking the witness does not require an MILP solver.

  axiom_rewrite/
      The mathematical PA proof-translation theorem, source-pinned formula
      emitter, twelve explicitly equivalent gate words, and independent audit
      of the exact word used in grammar67. Includes the retained upstream
      proof-template sources needed to inspect the bootstrap argument.
      Also includes a common-core countermodel to a tempting factor movement
      and an independent audit of the entire distributed198 source and startup.

  distributed198/
      Complete new 198-state binary table, native/dense conjugacy, compiler,
      source, exact formula word, full instruction-frame verifier, and startup.
      The dense start is 0, interpreter root 75, and halt 198. All 4908
      symbolic contracts and the 58154-step exact blank startup pass.

  shared_helper/
      Two folds with one new helper: 13,660,768 restricted and 218,572,288
      generalized patches, no survivor in the specified two-cell/64-step
      simulation family. C++20 sources, pinned table, and replay wrapper.

  source_rotations/
      Source reassociation search that permits relative jump depths to change
      while requiring the complete ordinal instruction/control graph to agree.
      Includes the first-step and restricted second-step search receipts.

  repair_obstructions/
      Small, independently replayed two-trace certificates excluding one
      additional row repair for five specified failed one-state quotients.
      This is not a lower bound on general 195-state machines.

  verify_all.py, verification_summary.json
      Portable verifier wrapper and recorded result. The wrapper must be run
      without Python -O, because some inherited symbolic checks use assertions.

REPRODUCE
  Requirements: Python 3.10+ and the standard library for the certificate
  checks, plus a C++20 compiler for the shared-helper enumeration. A normal
  LaTeX installation with the packages used in report.tex is
  needed only to rebuild the PDF. No network access is needed for the checks.

  From this directory:
    python3 verify_all.py
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

  Individual verifiers can also be run directly. Checks regenerate their
  corresponding JSON receipts and, where stated, deterministic derived tables.
  SHA256SUMS records the delivered files; compare before running generators.

TABLE FORMAT
  Each noncomment line in a .tm file is:
    current_state read_bit write_bit direction next_state
  Bits are 0 or 1 and direction is L or R. Halting labels have no outgoing
  rows and are excluded from the working-state count. All machines use a
  blank two-way infinite binary tape and move exactly one cell at every step.

SOURCE REVISIONS
  jamesyc/BusyBeaver PA196:
    407cdc356f6b586635e71ac92be394255f4bfea4
  jamesyc/BusyBeaver PA209:
    69d98241a721ead20b4f0b17df9062950b40fbfe
  VladimirReshetnikov/ProveIt:
    f1f076e31995f10460838d1846456f4bb9c8ae80

The supplied reference programs and tables retain their original notices.
The symbolic runtime is adapted from the cited ProveIt incoming research
archive and ultimately from Chang's M6 runtime contracts. The original proof
libraries are referenced at these pins; they were not rebuilt in this work.
