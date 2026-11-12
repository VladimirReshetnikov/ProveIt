SCALAR ITERATION UNIQUENESS FOR iPRA
Research report for Vladimir Reshetnikov, November 11, 2026

START HERE
report.pdf is the complete mathematical report.
report.tex is a standalone LaTeX source; it needs no other local TeX files.
The source can be rebuilt from report_front.tex, ur_complete.tex,
ur_retraction.tex, ur_predecessor.tex, ur_reflection.tex, and report_back.tex
by running python3 build_report.py.

MAIN RESULT
In the original scalar term language x,0,S,I(n,a;u.h), contextual
literal-equation induction is equivalent to this single uniqueness rule:

   Gamma |- f(Sz) = h(f(z))
   ------------------------------------------- UR
   Gamma |- f(t) = I(t,f(0);u.h(u))

The update has one scalar state and no active counter argument. The
premise contains no induction hypothesis. The seed is determined by f.
The full theorem applies under arbitrary retained first-order contexts,
with the usual eigenvariable restrictions. Both numerical domains are
whole, equality is actual equality, and the bi-interpretation composites
have graph x=y. The scalar-to-iPRA bridge is inherited after equation
induction has been recovered independently.

The new proof closes the explicit bootstrap gap in the incoming
scope_kernel package: a modified scalar ramp gives predecessor by UR;
Boolean diagonal descent and an explicit scalar accumulator give faithful
equality reflection; the inherited retraction argument then restores
general equation induction.

SIMPLICITY AND LIMITS
This is a mathematical alternative that removes induction as a primitive.
It does NOT establish a smaller complete checker for the new arithmetic.
The matched raw checker increases from 3322 to 3393 normalized Python
bytes. Both complete modules and measurements are included.

A separate implementation refinement of the EXISTING calculus reduces
the full validated lexical checker from 870 to 866 normalized bytes.
It reuses the first kernel scope traversal and preserves the public
input contract. It does not implement UR or change the axiomatization.
No global minimum, historical priority, or absolute simplicity is claimed.
In particular, the distinct 516-byte guarded profile in the repository
has not been beaten.

The new universal theorem is a written proof, independently reviewed at
its main dependency boundaries. It is NOT a new Lean/Rocq formalization.
Finite tests are supplementary checks, not a proof in nonstandard models.

COMPLETE CHECKERS
code/uniqueness/scalar_ur.py       New eight-pattern native UR calculus.
code/uniqueness/baseline_qi.py     Matched induction control.
code/uniqueness/README.md          Exact tagged syntax and instructions.
code/compact/checker.py           866-byte unchanged-calculus refinement.
code/compact/control.py           Exact 870-byte upstream control.
The two pairs use different public certificate formats.

RUNNING AND REPRODUCING
Python 3.12.14 is the reference measurement environment.
All code uses only the standard library.

   python3 reproduce.py
   python3 reproduce.py --pdf

The second command also assembles and compiles the PDF using pdfLaTeX.
To compile report.tex directly:

   pdflatex -interaction=nonstopmode -halt-on-error report.tex
   pdflatex -interaction=nonstopmode -halt-on-error report.tex

An example complete UR proof can be checked with:

   python3 code/uniqueness/scalar_ur.py < code/uniqueness/examples/scalar_ur_ur_identity_at_closed_numeral.json

Acceptance is exit code zero with exactly ACCEPT on standard output.
The old compact codec has its own documented integer/list proof format.

CONTENTS AND PROVENANCE
reference/ contains the exact inherited mathematical source files used
in the bridge, the prior incomplete UR note, and the upstream license.
evidence/ contains numerical results, the scoped incoming-package audit,
source provenance, and reproduction results.
tests/ contains finite arithmetic checks.
CLAIMS.json separates established claims from limitations.
SHA256SUMS.json identifies the final delivered bytes.

Repository snapshot:
11be5aabc6b07262046e2553419bc6b05271d178
https://github.com/VladimirReshetnikov/ProveIt/tree/11be5aabc6b07262046e2553419bc6b05271d178/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The six incoming packages were inspected before selecting this direction.
The report includes Further research questions.
