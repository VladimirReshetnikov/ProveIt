FRESH ALIASES AND BACKWARD SUBSTITUTION FOR iPRA
Research package prepared for Vladimir Reshetnikov, 12 November 2026

STATUS
======

The normalized-byte record improves from 487 to 479. Separately, this package
gives a new raw Alias/Back presentation proved equivalent to full iPRA, but
its checker is larger. A new mathematical axiomatization that also improves
the global checker benchmark has not been established.
The new mathematical calculus is not the calculus of that 479-byte program.
No new theory below all current coordinate minima, global optimum, arithmetic
axiom deletion, or new Lean/Rocq verification is claimed.

START HERE
==========

ipra_alias_back_2026-11-12.pdf   Compiled research report.
ipra_alias_back_2026-11-12.tex   Complete standalone LaTeX source of the report.
CLAIMS.json                    Machine-readable result and limitations.
evidence/metrics.json           Reproduced whole-program measurements.
evidence/reproduction.json      Offline validation receipt.

THE NEW MATHEMATICS
===================

On raw scalar iterator terms, use two equality schemes:

    Back:   Gamma |- b=t, Gamma |- F[t/b]  =>  Gamma |- F
    Alias:  Gamma,b=t |- F                =>  Gamma |- F[t/b]

In Back, b is the newest current parameter. In Alias, b is new and its
defining term t is in the outer scope. Substitution is capture avoiding and
simultaneous once. Back's replacement may contain its source; Alias's may not
contain its fresh parameter.

Alias alone derives reflexivity by exporting its hypothesis b=t as t=t.
The two schemes derive symmetry and full equality transport with no
arithmetic, normalization or induction. An explicit generalized compiler
restricts every Back source and every clause specialization to the newest
parameter. It recompiles source premises inside larger alias scopes rather
than assuming that an existing restricted proof can be weakened unchanged.
The complete presentation can restrict Back to equations, by a compiler
invariant. Alias remains available for compound exported formulas; restricting
Alias to equations as well is not established for fixed specialization.

Both computation equations, Open and witness-selected Close are retained.
The Close witness is still an arbitrary term. All numerical domains and
the ordinary formula reading are unchanged. Composing the proved consequence
equivalence with the pinned native/iPRA bridge gives both whole-domain
interpretations, actual equality, and identity numerical round trips.

NEW RAW ACCEPTANCE PROGRAMS
==========================

raw_basis/code/raw_alias.py          Readable complete final checker.
raw_basis/code/raw_alias_small.py    Same calculus with shorter scope/CLI code.
raw_basis/code/raw_alias_unrestricted.py
                                    Intermediate unrestricted Back/Use calculus.
raw_basis/code/raw_template_matched.py
raw_basis/code/raw_template_small.py Matched old template controls.
raw_basis/code/translate.py          Untrusted compilers, replayed by the kernels.
raw_basis/RAW_THEOREM.md             Exact seven rule patterns and compiler proof.

These programs use tagged JSON proof trees and validate their closed public
goal and all active term, formula, clause-index and scope data. An unused
premise placeholder of antecedent-free Use is ignored, as in the control.
No computation normalization is performed. Only standalone acceptance modules,
not producers or the report, are included in the following measurements:

                                     Tokens   AST   Normalized bytes
Readable matched template                764   883       2918
Readable Alias/newest                    825   966       3149
Short matched template                   716   838       2683
Short Alias/newest                       773   916       2903

The new interface currently costs MORE checker code. It must not be described
as a global size reduction or as the source of the 479-byte record.

THE SEPARATE 479-BYTE RESULT
===========================

code/checker_479.py        New exact refactor of the inherited guarded checker.
controls/checker_487.py    Byte-for-byte current incoming byte-profile control.
proofs/inline_validation_proof.txt
                          Universal finite-execution preservation argument.

                                     Tokens   AST   Normalized bytes
Current token incumbent                  248   277        609
Current AST incumbent                    254   270        608
Current byte incumbent                   276   308        487
New byte refactor                        272   304        479

The compact coordinate envelope was (248,270,487), in different programs.
Only its byte coordinate is improved. The 479-byte program preserves the
multiline JSON interface, four-field certificate protocol, every scope scan,
and every finite successful trace of the 487-byte control. It removes an
always-true test of a newly created function object.

Its contract assumes finite integer/list certificates and a canonical closed
guarded Eq/D public goal; a separate public-grammar validator is not included.
Do not compare this module directly with a fully validating native checker
without stating the different contract. Acceptance requires normal exit and
exactly ACCEPT followed by a newline. Exceptions reject; unused input prefixes
retain the inherited convention.

SUPPORTING ARTIFACTS
===================

equality_audit/            Independent Hyp/Alias/Back fragment verifier and
                          finite certificates; not a complete iPRA checker.
supplement/two_field/      A new two-field codec of the existing full-normal
                          conditional-copy calculus. It is 609/699/1644,
                          against a matched 629/732/1715 tree control.
reference/                Frozen attributed upstream foundations and license.
tests/scope/              A known false certificate rejected by both byte
                          programs; the deliberately unsound checker is omitted.

The two-field codec is separate from the raw Alias theory. It has normalizing
syntax and a different input contract. Its exact tree/stream translators and
strict acceptance program are included, but no compact record is claimed.

The exact mathematical/protocol foundation of the 479-byte checker is in
reference/upstream_guarded_theory.tex and upstream_certificate_protocol.tex.
The chain of accepted context and evaluation rewrites is in
upstream_context_compositions.tex and upstream_single_binder_proofs.txt;
reference/upstream_chain/ supplies the intermediate control programs.
evidence/COMPACT_SOURCE_CHAIN.json records their exact pinned source identity.

REPRODUCE
=========

    python3 verify_manifest.py
    python3 reproduce.py

Use CPython 3.12.14 to reproduce the exact source measurements. Another Python
version may change ast.unparse formatting. The reproduction requires only the
standard library and no network. It executes the complete checkers normally
and with -O, checks source hashes, replays inherited and translated proofs,
and regenerates evidence. The delivered run completed 886 checker processes
with no failures. Finite tests supplement the written general proofs.

The root manifest covers files as delivered. Run manifest verification before
regenerating evidence or rebuilding the PDF, which can intentionally change
recorded bytes. The scripts do not modify any source repository.

PDF BUILD
=========

    python3 build_pdf.py

The helper tries installed pdfLaTeX, then (only if needed) generates a private
format from installed TeX sources. It downloads nothing and changes no global
TeX configuration. A conventional complete TeX Live installation is required.
The report source is self-contained and does not input the reference excerpts.
The frozen upstream chapter files are reference sources, not standalone TeX
projects; their original preamble is supplied for context.

PROVENANCE AND ASSURANCE
=======================

Repository: VladimirReshetnikov/ProveIt
Commit: 36d37fc1071fe289371f6bcd7dcfa0eac593a5a6
Scope: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The audit includes all nine incoming archives at this head. Evidence includes
the 3,991-path source census, verified Git identities, and the exact current
frontier. All claimed theorem equivalences have written arguments. The new
Python code, compilers and equality rules have not been formally verified in
Lean or Rocq. The old formalized bridge is cited with its actual scope.

Further research questions are in the report. They include fusing scope rules
without compromising freshness, reducing the equality interface further,
eliminating the remaining Close witness, formalizing the generalized compiler,
and obtaining a mathematical change that truly reduces the whole checker.
