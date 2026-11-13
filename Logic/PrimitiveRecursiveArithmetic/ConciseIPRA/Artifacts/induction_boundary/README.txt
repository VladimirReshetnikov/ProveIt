NONSTANDARD PARAMETERS DO NOT RESCUE THE NUMBERING THEORY
13 November 2026

STATUS
The requested positive axiomatization below the current ConciseIPRA
complexity envelope was not established. This archive must not be cited as
a smaller positive iPRA presentation or as a new checker-size record.

MAIN RESULT
The report answers the pinned article's question "Parameters for the
numbering theory" negatively. The existing theory T_cal has a model with
nontrivial involutions fixing every finite tuple, while preserving ALL
numbering laws I(n,k;u.Su)=S^k n for fixed standard k. Nonstandard parameters,
finite-dimensional definable domains and definable quotients therefore
cannot supply an ordinary bi-interpretation with iPRA (with realized or
provably inhabited parameter conditions).

The model also validates successor injectivity, computation, coverage,
separation, identity iteration, extensionality, every fixed-point law,
and constant-target induction. It even supports induction for quantified
constant-target formulas, as an optional model strengthening.

Put C(v,a,b)=I(v,a;w.b) and H(u)=S C(u,1,u). The literal equation
I(Sn,0;u.H(u))=S(Sn) has derivable base and step but fails at colored
nonstandard inputs. The usual numbering law I(n,0;u.Su)=n REMAINS TRUE.

READ
  report.pdf              Compiled complete report.
  report.tex              Main LaTeX source.
  sections/obstruction.tex Complete new model construction.
  STATUS.json             Precise machine-readable claim boundaries.

REPRODUCE (CPython 3.12.14 for exact source-size normalization)
  python3 code/reproduce.py
  python3 code/finite_checks.py
  python3 code/survey_incoming.py --archives /path/to/the/five/zip/files
  python3 code/build.py

If --archives is omitted, survey_incoming.py downloads only the exact
pinned public repository archives and checks their Git blob hashes.
It does not execute their Python programs. The build requires pdflatex
and the packages named in report.tex.

CONTROLS
Six programs under controls/ are copied byte-for-byte from the pinned
repository's existing incoming packages. Their source hashes and paths
are in evidence/controls_provenance.json. They are not new checkers.
The compact envelope is 239 tokens / 256 AST nodes / 461 normalized bytes;
the strict native envelope is 317 / 356 / 597. Different programs attain
these coordinates. Neither is a proved universal complexity lower bound.

VALIDATION LIMITS
The infinite countermodel and the interpretation argument have written
proofs and independent mathematical review. No Lean/Rocq formalization is
provided. finite_checks.py checks supporting finite facts, not the whole
model. Benchmark measurement does not prove checker soundness.

COMPARISON SNAPSHOT
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 798856e4ef2d02b7f9c0f1660828c5ce58f277f2
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The report distinguishes inherited constructions and methods from the
new equivariant combination. Further research questions appear in its
final section. No GitHub repository files were changed by this work.
