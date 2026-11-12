A 50-NODE SCALAR PREDECESSOR FOR iPRA
Research iteration, 12 November 2026

STATUS OF THE REQUESTED TARGET
==============================
This package does not establish an axiomatization below the current
complete-proof-checker frontier. It provides a substantive arithmetic-term
reduction inside the existing iPRA presentation, and a separate minor exact
checker refinement. Neither is presented as a new globally smallest theory.

MAIN RESULT
===========
A predecessor term using only variables, zero, successor, and scalar
iteration has 50 fully expanded constructor nodes, versus 57 in the newest
incoming proposal. The paper proves P(0)=0 and P(Sx)=x using computation,
equality, and literal-equation induction, before coverage, separation,
successor injectivity, equality reflection, pairing, or general primitive
recursion. An absorbing factor map and selector duality give the saving.

The inherited single-binder universal macro consequently saves seven nodes
per substituted variable occurrence. Its comparison family changes from
67n+4 to 60n+4 raw Eq/D formula nodes, with unchanged binder rank.

CHECKER RESULT
==============
The complete stream checker control has 244 tokens, 272 AST nodes, and 608
normalized bytes. One exactly justified expression rewrite gives 244 tokens,
273 AST nodes, and 607 bytes. It has the same finite exact-integer/list
acceptance relation and the same input/output protocol. This does not beat
the current documented coordinate envelope (244,267,478), whose coordinates
are attained by different programs under their stated compact contracts.

CONTENTS
========
ipra_pred50.pdf                 Compiled article.
ipra_pred50.tex                 Main LaTeX source.
sections/                      All included source sections.
code/arithmetic/pred50.py       Expanded-term builder, two syntax counts,
                               scope audit, literal and fast diagnostics.
code/arithmetic/universal_sizes.py
                               Independent formula-expansion size audit.
code/checker/checker607.py      Complete factored checker.
code/checker/control608.py      Exact matched control.
code/checker/verify.py          Metrics, AST rewrite audit, differential tests.
code/checker/rewrite_proof.txt  Operational equivalence proof and contracts.
code/checker/fixtures/          27 JSON-line certificates.
reference/checkers/            Three copied compact frontier profiles.
reference/                    Inherited arithmetic and logical proof sources,
                               source provenance, and upstream license.
evidence/                     Results, explicit syntax trees, source inventory,
                               and two independent in-run review notes.
CLAIMS.json                   Machine-readable claims and nonclaims.
reproduce.py                  Standard-library reproduction entry point.
MANIFEST.sha256               Checksums for every delivered file except itself.

REPRODUCE
=========
From this directory:

    python3 reproduce.py

The reference measurement runtime is CPython 3.12.14. This runs the arithmetic
and formula audits, checks all selected source metrics, and compares both
checker programs on 27 fixtures in ordinary and optimized Python.

To additionally compile the article with a normal LaTeX installation:

    python3 reproduce.py --pdf

The main LaTeX source needs the supplied sections/ and code/ files. No
network access is needed by the reproduction scripts.

To run one positive certificate directly:

    python3 code/checker/checker607.py < code/checker/fixtures/global_computation_zero_global.jsonl

Success is the exact line ACCEPT. The compact checker assumes its advertised
canonical guarded public goal grammar and finite integer/list certificate
alphabet; it does not claim full validation of arbitrary JSON or unread
suffix text. Read the paper's public-language section before generalizing
its scope to other formulas.

PROOF STATUS
============
The new universal result is the written equational proof. Literal execution
at inputs 0..6, a 5x7 comparator grid, and 1,840 additional finite identities
are implementation diagnostics, not a universal proof. Two independent
agents in this research run reviewed the mathematics. This is not external
peer review, and there is no new Lean or Rocq formalization.

The ordinary theory and its whole-domain bi-interpretation with full
first-order intuitionistic PRA are inherited. The archive states the entire
native syntax and rule system, gives all logical macros, specifies ordinary
logical/nonlogical axioms, and explains both term and formula round trips.
Both numerical interpretation domains are whole and their comparison graphs
are x=y. Replacing the predecessor by P50 preserves this bridge.

PROVENANCE
==========
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: b9aa36102e523213ae956b474ec651bfde3e5665
Scope: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA, including docs/incoming.
The directory and the incoming packages were read; no remote change was made.
The clock/ramp and P57 are attributed to the incoming predecessor57 package.
Source hashes are recorded. Materials may be used under the MIT No
Attribution license included at reference/LICENSE-ProveIt.txt.
