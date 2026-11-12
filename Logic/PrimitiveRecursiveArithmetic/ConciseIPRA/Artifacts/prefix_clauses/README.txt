A PREFIX PRESENTATION OF INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Prepared for Vladimir Reshetnikov, November 11, 2026

START HERE

Read ipra_prefix_clauses.pdf. Its self-contained editable LaTeX source is
ipra_prefix_clauses.tex. The modular source is report.tex plus paper/.

RESULT

Every native Eq/D formula is a chain of D binders ending in one equation.
The primary calculus stores it as [k,s,t], meaning D^k(s=t). Only numerical
term syntax remains recursive. Formula opening acts on two terms at an
index calculated from k. The complete calculus has four instruction
families (Use, Eval, Elim, Intro) and one fixed reflexivity clause.

The existing four-family inference basis is inherited, not claimed new.
The primary improvement is a simpler formula and certificate interface,
with a smaller complete implementation than the inspected uniform_clauses
program. The report proves exact derivation correspondence and composes it
with the existing whole-domain bi-interpretation with iPRA. Equality is
actual equality, and both numerical composite isomorphisms have graph x=y.

A separate theorem removes clause antecedent fields altogether, by encoding
facts as conditional closures with an asymmetric iterator gate. Its proof
is in the appendix and its checker is included, but that implementation is
larger than the primary paired-clause implementation.

MEASUREMENTS AND LIMITS

Complete module                 Tokens   AST nodes   Normalized bytes
Existing uniform_clauses          807        931           2912
Matched nested control           791        890           2763
Primary prefix checker           788        900           2700
Homogeneous prefix alternative   840        965           2843

The primary program improves all three coordinates against the exact
existing four-family program. Against the tightly matched nested control,
it saves 3 tokens and 63 bytes but has 10 more AST nodes.

THIS IS NOT A NEW GLOBAL MINIMUM. The repository already has a 788-BYTE
validated native checker and a 516-byte compact checker with a distinct
canonical-public-goal contract. The 788 in the primary row above is a TOKEN
count; that program has 2700 normalized bytes. Those smaller existing
sources are included in reference/ so this distinction can be inspected.

The new metatheorems are written mathematical proofs, not newly checked
Lean or Rocq proofs. The inherited native equivalences and arithmetic
bi-interpretation have Lean formalizations in the pinned repository.
Only selected exact Lean reference files are included here; they are not
a complete standalone Lean workspace.

RUNNING THE CHECKER

Requires Python 3.10 or later for structural pattern matching. Measurements
and delivered evidence use CPython 3.12.14. No third-party Python package
is required.

From this directory:

  python3 code/flat_control.py < code/examples/equation_induction.json
  python3 code/reproduce_checker.py
  python3 code/audit_flat.py code/flat_control.py
  python3 code/audit_homogeneous.py

The first command prints ACCEPT. The second regenerates the certificates,
normalized sources, metrics, and cross-check evidence under code/evidence/.
The third reruns the independent binding and scope audit and writes
code/flat_audit_results.json. The fourth checks the homogeneous gate and
its supplied equation-induction certificates.

The prefix checker filename flat_control.py is retained consistently across
all measurement scripts and recorded hashes; it is the primary new checker.
nested_control.py is the matched nested-formula comparator.
reference_uniform.py is the exact existing upstream checker.
flat_homogeneous.py implements the proved antecedent-free alternative.

VERIFICATION

Delivered evidence records 37 positive certificates, each translated to
three checkers and run with ordinary Python and python -O; 22 negative
inputs in both modes; 266 subprocess expectations; and 2001 checks that
opening commutes with expansion. All passed.

An independent environment-semantics audit passed 400 matrix openings,
400 witness openings, 300 iterator-body substitutions, 20 rejection
attacks, and 5 accepted examples. A separate homogeneous check passes
400 gate formulas at zero and at 800 positive-control instances, plus
6 closed certificates including induction with gate-based retrieval.
These finite checks supplement the
written proofs; they do not establish universal metatheorems by testing.

The Use premise payload is intentionally ignored when the antecedent has
identical leaf terms. Examples put [] there. This is part of the specified
format, not a hidden claim that ignored payloads are valid proof trees.
All active proof fields, public goal grammar, term scopes, and eigenvariable
conditions are checked. See code/FORMAT.txt.

Completeness concerns the ideal finite-derivation algorithm. A concrete
Python process has parsing, recursion, integer, and memory resource limits.
The binder count can compactly encode a very long finite D prefix.

BUILDING THE PAPER

  python3 build.py

This flattens the modular LaTeX and runs pdflatex twice. Alternatively, run
pdflatex twice directly on ipra_prefix_clauses.tex; it contains its own
bibliography and requires no external graphics or input files.

PACKAGE CONTENTS

  ipra_prefix_clauses.pdf/.tex  Complete report and standalone LaTeX source
  report.tex, paper/           Modular source
  code/                       Standalone checkers, translators, generators
  code/examples/              Seven primary and six homogeneous certificates
  code/evidence/              Full metrics and subprocess results
  evidence/                   Independent audits and build/render records
  reference/                  Pinned upstream sources and MIT-0 license
  CLAIMS.json                 Machine-readable claim and limitation summary
  PROVENANCE.json             Source paths, pinned commit, content hashes
  SHA256SUMS                  Hashes of all other package files

SOURCE SNAPSHOT

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 17898ea7e6a1300dfdcad71040d5daeed67916d4
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The report includes explicit logical and numerical rules, derivations of
equality and computation, the restricted induction interface, both
interpretation composites, measured comparison limits, and further research
questions.
