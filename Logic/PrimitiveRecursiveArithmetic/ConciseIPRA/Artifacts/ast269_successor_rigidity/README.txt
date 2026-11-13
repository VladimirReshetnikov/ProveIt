CONCISE iPRA: AST269 AND SUCCESSOR RIGIDITY
Prepared November 12, 2026 (Pacific time)

Read report.pdf. Its LaTeX source is report.tex.

CONFIRMED CHECKER RESULT
  complete standalone checker: 255 tokens / 269 AST nodes / 605 bytes
  exact matched control:       255 tokens / 271 AST nodes / 606 bytes

These are CPython 3.12.14 ast.unparse-normalized measurements. The program
uses one whole JSON input value, the unchanged three-field certificate
format, and exactly ACCEPT followed by LF on success. It checks the
inherited guarded native calculus. It assumes the same integer/list
alphabet and canonical guarded public-goal contract as its control; it
does not separately validate the whole public grammar or input alphabet.

The pinned corpus's whole-JSON compact coordinatewise envelope was
249 / 271 / 477, attained by different programs. The delivered refinement
improves only its AST minimum, yielding 249 / 269 / 477 for the enlarged
family. It does not beat the token or byte records. No absolute minimum
or program below all old minima has been established.

MATHEMATICS
The report also gives a fully specified successor-rigidity presentation
with an explicit Boolean equality split and counter-aware recursor. It
proves contextual quantifier-free induction by one rigidity application,
then proves whole-domain bi-interpretability and equiconsistency with iPRA.
This is a synthesis of existing retraction and equality-split ideas.

The 269-node checker implements the EXISTING native calculus, not the new
rigidity presentation. No checker-size benefit is claimed for the latter.
The new mathematical proofs are written proofs, not a new Lean or Rocq
formalization. Finite executions are regression evidence, not proofs of
the general soundness theorem.

RUN
  python3 checker/verify.py
  sh build.sh

The verifier measures both complete programs and runs 20 fixtures through
both in normal and optimized Python: 80 isolated executions. The recorded
run had zero failures. Some positive regression inputs use auxiliary
Q-root formulas; they are not all public guarded goals.

The report builds with pdflatex (three passes) and standard LaTeX packages.
The checker and verification scripts use only Python's standard library.
No network access or repository download is needed for checker validation
or PDF rebuilding. To repeat the full corpus census, point evidence/census.py
at a local checkout of the pinned repository as documented in that file.

BASELINE
  repository: VladimirReshetnikov/ProveIt
  commit: 12197d86f63e9ec73b2d91399c4de2a8cb0077ee
  project: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
  measured Python files: 2,894; parse failures: 0

See CLAIMS.json for exact claim boundaries, checker/PROVENANCE.json for
source provenance, evidence/benchmark.json for incumbent metrics, and
MANIFEST.sha256 for archive integrity. Further research questions are in
the report. Inherited files retain their MIT-0 attribution.
