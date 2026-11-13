SCOPE RESERVATION AS THE VALIDATION PHASE FOR iPRA
13 November 2026
================================================

RESULT AND LIMIT

This package gives smaller fully validated proof-checker presentations of the
existing native scalar calculus, with a proved scope/validation invariant.
It does not give a new arithmetic axiom basis or meet the stronger request for
one construction below all current complexity minima.

The new strict whole-JSON Eq/D envelope is 302 tokens / 340 AST nodes /
584 normalized bytes, against 306 / 348 / 589. Different complete programs
attain these minima. The entry-reservation-only envelope is 304 / 340 / 584.
The compact cross-contract extrema 239 / 255 / 461 are not beaten.

Read ipra_scope_phase.pdf or its self-contained ipra_scope_phase.tex for the
complete calculus, imported bi-interpretation, new scope proof, comparisons,
counterexamples, and further research questions.

DELIVERED CHECKERS

  code/checker_tokens302.py        302 / 352 / 646
    Three fields, direct leaves, explicit phase bit, reservation at return.
  code/checker_ast340.py           314 / 340 / 681
    Three fields, direct leaves, reservation at entry; no independent phase bit.
  code/checker_bytes584.py         311 / 362 / 584
    Four fields, eager opener, reservation at entry; no independent phase bit.
  code/checker_entry_tokens304.py  304 / 349 / 646
    Three-field entry version without the AST-oriented structural binding.

The 584-byte program dominates the previous byte winner (324 / 367 / 589)
in all three coordinates. No single delivered program is below all three
coordinates of the previous strict envelope.

All checkers read one complete JSON value, validate its integer/list alphabet
including unused prefixes, and validate the closed native Eq/D public goal.
They print ACCEPT on normal acceptance. Their ordinary realization is the
same whole-domain, actual-equality theory as the source native calculus.
New certificates require recompilation because fresh names are allocated
at different points. Equality of arbitrary raw accepted inputs is not claimed.

REPRODUCTION

Use CPython 3.12.14 for the recorded source normalization and measurements.
The reproduction scripts use only the Python standard library.

  python3 reproduce.py

This verifies frozen artifact hashes, measures ten complete new/control
programs, recompiles the canonical fixtures, runs the correct checkers in
normal and -O modes, exercises scope/type/false-goal regressions, and replays
the deliberately unsound diagnostic controls. The recorded run has 806
isolated processes and zero unexpected outcomes. Acceptance by a file named
UNSOUND_... is an expected demonstration of an invalid reordering, not a theorem.

Build the report with a standard TeX installation:

  latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_scope_phase.tex

If the installed TeX sources have no format cache, the included fallback is:

  python3 build_pdf.py

It uses installed sources and a private temporary format; it downloads nothing.

The primary .tex source is self-contained apart from standard TeX packages.
No reference chapter, generated metric file, or external code listing is
required to compile that report.

LAYOUT

  code/          Complete trusted checkers and untrusted verification/compilers.
  certificates/ Canonical translated examples plus malformed and false cases.
  diagnostics/  Explicitly unsound negative controls and minimal attacks.
  evidence/     Execution receipts, measurements, and independent written audits.
  reference/    Exact attaining upstream controls, source fixtures, full pinned
                unified article source, provenance manifests, MIT-0 license.

FOUNDATION AND STATUS

Repository: VladimirReshetnikov/ProveIt
Source pin: 7a7633980dbca7f599322a5e7f1e65fb1cddb7c8
The pending checked_reduction and validated_three_field archives are included
in the baseline audit. Main later advanced to efe8812fb3d9b9d09d1d24b9f6eaf052a0eb5200
to land those same deliveries, without an additional unseen baseline change.

The bi-interpretation of the native scalar calculus with first-order iPRA
is inherited from that development. The new contribution has written proofs
and executable regressions, not a new Lean/Rocq formalization. Finite tests
support the implementation; they are not proofs of the universal metatheorems.

Source-derived material retains the upstream MIT No Attribution license in
reference/LICENSE-ProveIt.txt. The reference article records its own provenance.
