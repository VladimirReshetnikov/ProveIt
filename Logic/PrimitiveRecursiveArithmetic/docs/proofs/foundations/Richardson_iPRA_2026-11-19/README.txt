RICHARDSON'S THEOREM IN INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
===================================================================
Prepared for Vladimir Reshetnikov, 19 November 2026.

START WITH report.pdf. The complete LaTeX source is report.tex plus sections/.

MAIN RESULT
The report gives a constructive arithmetical proof of Richardson's identity
undecidability theorem. Its explicit analytic reduction uses only rational
constants, pi, the variable, addition, multiplication, sine, and one outer
absolute-value occurrence. Exponential and log(2) are not needed.

A natural polynomial root is equivalent to an existential strict rational
nonzero-evaluation certificate. Taking negations gives identity iff absence
of a root. The established Gaifman--Dimitracopoulos formalized MRDP theorem
in I-Delta-0 + EXP, followed by negative translation, calibrates absence of
a root with nonhalting. The final diagonal argument is intuitionistic and
requires neither Markov's principle nor positive MRDP witness extraction.

PROOF STATUS
The human proof uses the explicitly cited established formalized-MRDP
metatheorem. It is not a new proof of MRDP. It establishes an iPRA derivation
by proof translation, but no serialized derivation or fixed universal MRDP
polynomial is supplied.

lean/ contains exact syntax and a fully written constructive parametric
logical core, together with a detailed object-language formalization plan.
The Lean source was NOT COMPILED. The full Prf PRAAx endpoint is outstanding.
The logical core has explicit structure assumptions for arithmetic/analytic
representation and simulation; these assumptions are not disguised proofs.

code/ contains a polynomial-to-expression compiler and exact rational interval
evaluation. It is not an identity decision procedure or universal MRDP compiler.
Four examples and exact certificates are included. All 14 implementation
checks passed. The global proof does not depend on numerical experiments.

REPRODUCTION
  bash build.sh
  python3 code/test_certificates.py
  python3 code/richardson.py demo --output code/demo_results.json
  python3 code/richardson.py evaluate code/examples/linear_root.json --x 1.11415714087193 --bits 48

A normal TeX Live installation with pdflatex or latexmk is sufficient for the
PDF. Python needs only its standard library (3.10 or newer). Lean 4 is needed
to check the standalone Lean source; see lean/README.txt. A full iPRA proof
requires the ProveIt integration work listed in lean/FormalizationPlan.txt.

PROVENANCE
ProveIt was inspected at eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98.
No repository mutation or publication was performed. See evidence/ for source
records, the verification receipt, and independent review notes.
