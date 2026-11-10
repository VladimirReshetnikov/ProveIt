BOUNDED INITIALIZATION FROM A TIED SEED
Research prepared for Vladimir Reshetnikov, 10 November 2026

START HERE

Read report.pdf. The complete editable source is report.tex with the theory/
and reference/ inputs. All inputs needed to compile the report are included.

This package contains two explicitly separate results.

1. A mathematical construction: the theory T_{B epsilon} has a recursor whose
   seed is tied to its update, a Boolean numerical test of actual equality,
   separation, and contextual literal-equation induction. Ordinary intuitionistic
   first-order logic is part of the presentation. The report proves full
   whole-domain bi-interpretability with first-order iPRA, with identity maps
   for both return interpretations. Successor is itself definable, so the
   primitive numerical grammar can use only 0, epsilon, and the staged B
   constructor. The key steps are bounded initialization, a compiler with
   internal majorants and cap coherence, and finite quantifier-free function
   graphs that preserve induction. Coverage and quantifier-free induction
   are derived. This is a written mathematical proof, not a proof-assistant
   formalization or an executable general proof translator.

2. A measured implementation improvement for the INHERITED initialized-iterator
   Choice-DI calculus. These checker sizes do not measure the new arithmetic
   theory. The program family improves all three observed coordinate minima
   of the supplied corpus, across different programs. It does not produce
   one program below all three old minima.

COMPLETE-PROGRAM MEASUREMENTS

Program                              Norm. bytes  Tokens  AST  Raw gzip-9
Current byte leader                         616     269   311     366
Current AST/token leader                    649     268   300     367
code/checker.py                              612     266   310     360
code/checker_compact.py                      604     266   312     356
code/checker_ast.py                          639     267   298     360

Old family coordinate minima: 616 / 268 / 300.
New family coordinate minima: 604 / 266 / 298.
Neither triple is the measurement of one program.

Use code/checker.py as the recommended transparent implementation. The compact
variant uses the inherited exact-JSON-list predicate a*0==[]. The ancillary AST
variant uses the inherited exception-dispatch approach. Nonempty strings reject
through CPython's finite recursion limit. Consequently it is not a structurally
terminating parser for all finite JSON in an ideal unbounded-stack interpreter.
This is the same qualification as the actual upstream AST leader; its additional
empty-iterable aliases and initialization expressions are documented and tested.
code/readable_checker.py explains the primary implementation and is not imported
by any compact program.

All measured modules include input loading, validation/opening, inference,
freshness, and the success verdict. A certificate is accepted exactly when the
process exits zero and prints the single line ACCEPT. Exceptions reject through
nonzero exit; no REJECT-printing wrapper is assumed for either new or baseline
programs. Python and its standard JSON implementation are the shared runtime.
Gzip is informational, not an optimization objective. The exact Python and zlib
versions, normalization convention, hashes, and compressed source files are given.

No absolute simplest axiomatization, absolute lower bound, or smallest complete
checker for the new arithmetic theory is claimed. The principal new mathematical
result and the modest implementation gains must not be conflated. External
literature-wide priority is not established by this research report.

REPRODUCTION

From this directory, using Python 3.12 (the recorded run uses CPython 3.12.14):

    python3 reproduce.py

This verifies the delivered manifest, reproduces the whole-module measurements,
checks compressed source identities, replays the checkers in ordinary and -O
Python, replays the frozen baseline fixtures, reviews the ancillary profile's
aliases and runtime behavior, and evaluates the tied-seed arithmetic macros.

Recorded evidence:
    172 main checker expectations, all passed.
    124 upstream minimum-attainer expectations, all passed.
    146 ancillary AST-profile review expectations, all passed.
    1102 finite arithmetic expectations, all passed; none skipped.

These suites overlap. Their counts are not claims of distinct mathematical
theorems. In particular, finite numerical examples do not verify the universal
compiler proof, nonstandard models, or the interpretation composites.

To inspect the measurements alone:

    python3 measure.py

To rebuild the PDF on a normal TeX Live installation with pdfLaTeX, AMS packages,
Latin Modern, microtype, hyperref/bookmark, listings, xurl, and the standard table
packages:

    python3 build.py

The script uses three pdfLaTeX passes with shell escape disabled. PDF metadata
and installed TeX versions can change the resulting PDF bytes. MANIFEST.json
describes the delivered files; rebuilding or editing files can therefore change
their hashes. To verify the original package, run reproduction before editing.

Example canonical certificate:

    python3 code/checker.py < examples/I0_arbitrary_seed.json

The successful result is ACCEPT. Certificate instructions are consumed from
right to left, with the goal as the last JSON element. See report.pdf for the
complete raw syntax, rule inventory, scope convention, and conservative meaning.

PINNED CORPUS AND OPTIONAL FULL AUDIT

Repository: VladimirReshetnikov/ProveIt
Commit: fb2dbd2a33c6b132671a54b029d0bf3cd98c633d
Directory: docs/drafts

All 13 direct archives were verified against their Git blob SHA-1 and byte size.
Recursive inspection covers 28 distinct ZIP payloads, 370 distinct Python sources,
and 165 nominal standalone public drivers. The inventory classifier is an aid,
not an automatic proof of correctness. Smaller non-driver helpers were inspected.
The complete census and immutable input URLs are in evidence/.

The original archives are not duplicated in this package. To reproduce the full
corpus census from local copies:

    python3 reproduce_corpus_audit.py --archives /path/to/docs/drafts

Or explicitly retrieve missing pinned files:

    python3 reproduce_corpus_audit.py --archives ./downloaded-drafts --download

This optional script verifies all direct archive identities, reads nested ZIPs
in memory, and never executes source code from the archives. It reconstructs
immutable commit URLs rather than relying on the original API metadata's main
branch URLs. Network access is required only when --download is supplied.

CONTENTS AND ATTRIBUTION

report.pdf, report.tex       Complete report and master source.
theory/                     New basis, proofs, exact expressivity result,
                            measured calculus, limitations, references.
reference/                  Exact attributed upstream metatheory and frozen
                            comparison programs; upstream license retained.
code/                       Three compact profiles, readable implementation,
                            and their deterministic gzip-9 source companions.
tests/, examples/           Executable controls and canonical proof examples.
evidence/                   Corpus identities, metrics, replay results,
                            source attribution, and review records.
CLAIMS.json                 Machine-readable statement of scope and limits.
MANIFEST.json               SHA-256 and length of each distributed file.

The basic tied-seed predecessor/gate/zero-start macros are inherited from the
local-scopes draft. The old scalar-iterator/Choice-DI interpretation metatheory
and its five appendices are attributed to the pinned predecessor package and
its named predecessors. The arithmetic contribution here is the bounded compiler,
its internal cap coherence, its finite-case induction transfer, and the resulting
whole-domain completion; the source theorem also gives the exact effective
one-coordinate-majorant term class. The checker contribution composes the
existing arity interface and predecessor supply, with measured implementation
variants. The report distinguishes each contribution from its prerequisites.
