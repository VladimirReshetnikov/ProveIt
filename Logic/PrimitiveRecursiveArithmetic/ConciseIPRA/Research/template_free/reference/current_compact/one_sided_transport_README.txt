ONE-SIDED TRANSPORT FOR CONCISE iPRA
Prepared for Vladimir Reshetnikov, November 11, 2026

RESULT
======
Replace the current seven-rule calculus's equality inference

    s=t, a(s)=b(s)  ==>  a(t)=b(t)

by one-sided crossed transport

    s=t, f(s)=r  ==>  r=f(t),   s is not the literal zero term.

Only f is a numerical template; r is an ambient numerical term. The
distinguished variable of f may be absent or repeated. Two applications
recover the old rule. All other rules, native syntax, ordinary QE, and the
single witness-selected introduction remain unchanged.

The written proof establishes exact equality of the consequence relations
for arbitrary contexts and native formulas. Both inherited iPRA
interpretations and both identity round trips transfer. Numerical domains
remain whole and equality remains actual equality. No standard-numeral
cut, quotient domain, uniform program evaluator, or stronger induction is
introduced.

A separate strengthening shows that the zero computation I0 and this
transport rule alone recover all equality reasoning, including zero-source
transport. Its proof uses neither induction nor logical rules.

MEASURED SIMPLICITY
==================
Matched complete implementations, differing only in their equality branch:

                         Tokens   AST nodes   Normalized bytes   gzip-9
Proposed C7                 1171        1339               3246      996
Existing-rule M7 control    1196        1364               3302     1005
Reduction                    25          25                 56        9

The byte reduction is 1.6959%. Both programs validate closed-goal syntax,
all consumed term/formula fields, and variable scope. Their equality opcode
is spelled x in both, so renaming contributes nothing to the difference.
Gzip is informational, not an optimization target. Raw source and normalized
gzip figures are both in evidence/measurements.json; exact compressed
source files are included in code/.

This is NOT a new compact-checker record. Current compact source profiles
include selected profiles attaining 257 tokens, 279 AST nodes, and 522 bytes
in different programs, under a different public-goal syntax contract.
Those sources are included and remeasured. There is no claim of an
absolutely simplest axiomatization or a substantial new global minimum.

START HERE
==========
report.pdf / report.tex           Standalone mathematical paper and source.
code/c7_checker.py               Proposed strict standalone checker.
code/m7_control.py               Matched control for the current rule.
code/FORMAT.txt                  Exact JSON grammar and all seven opcodes.
code/compare_checkers.py          Generates control by changing one branch.
evidence/matched_control.diff    Exact source difference.
evidence/measurements.json       Reproducible whole-module metrics.
evidence/*certificates.json      Positive and negative proof certificates.
evidence/*test_results.json      Test receipts.
formalization/NativeOneSided.lean Proposed Lean extension, NOT COMPILED.
reference/lean/                  35 exact pinned upstream Lean modules.
reference/baselines/             Exact comparison sources.
MANIFEST.json                    SHA-256 and size of all payload files.

REPRODUCE
=========
With Python 3.12 and the standard library:

    python3 reproduce.py

The command checks the manifest and source measurements, regenerates the
matched control in a temporary directory, and reruns both certificate
suites in normal and optimized Python. It does not modify the delivered
files. The C7 suite has 23 cases (10 accept, 13 reject); the M7 control has
25 cases (11 accept, 14 reject). Eleven certificates are identical between
the suites. There are also 1,200 independent denotational substitution
checks, including replacements under binders.

To print current metrics without writing files:

    python3 code/measure.py

To rebuild the PDF with a configured TeX Live or MiKTeX installation:

    python3 build.py

Rebuilding can change PDF metadata and its manifest hash. Verify the
distributed archive first or build in a copy. A standard installed TeX
distribution must provide the packages named by report.tex. No external
figures, bibliography service, shell escape, or network access is used.

STATUS AND LIMITS
=================
The main equivalence and its pure-equality strengthening are written
mathematical proofs with independent assistant review. Executable tests do
not establish the universal metatheorems. The proposed Lean extension has
not been compiled because this environment has no Lean executable. The
repository's inherited formalization was inspected and frozen, not rebuilt.
See formalization/README.txt for the exact intended compilation target.

Two X applications may duplicate the major proof s=t in a tree certificate.
No linear bound on serialized tree-proof size is asserted.

The current source snapshot is
8eb71c1e570e07ef45ead686628e77f18ef34798
https://github.com/VladimirReshetnikov/ProveIt/tree/8eb71c1e570e07ef45ead686628e77f18ef34798/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The GitHub repository was read without modification. Reference materials
retain their exact Git blob identities and the included MIT No Attribution
license. The proof-checker-size gain is local to the matched implementations;
the mathematical gain is the simpler one-template inference and equality
recovery argument. Further research questions are in the paper.
