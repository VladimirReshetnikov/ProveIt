SCALAR CONSTANCY FOR iPRA
Research report on the ConciseIPRA proposals
November 12, 2026

START HERE

Read report.pdf. The complete LaTeX source is report.tex together with
mathematics/*.tex. The two candidate proof checkers are in checkers/code/.
All files needed to rebuild the paper and repeat the packaged controls are
included. The original ProveIt checkout is needed only to repeat the full
source census.

RESULTS AND SCOPE

1. A scalar iterator, faithful Boolean equality, separation, a constancy
   rule, and the comparison equation delta(Sx,Sy)=delta(x,y) present full
   first-order intuitionistic primitive recursive arithmetic. The report
   proves bi-interpretability using the whole numerical domains and
   identity comparison maps, and hence equiconsistency. Quantifier-free
   induction, predecessor, coverage, a primitive-recursion compiler, and
   both interpretation round trips are supplied.

2. Omitting the comparison equation produces a theory that is not
   bi-interpretable with iPRA by ordinary finite-dimensional first-order
   interpretations, including definable subdomains, quotient equality,
   and finitely many parameters whose required conditions are provably
   inhabited. A three-copy model and a finite-order automorphism argument
   prove this. A modified model shows that the canonical successor-iterator
   equation does not repair the omission either. The modified model does
   not satisfy full mixed fusion; the original model does.

3. Two independent compositions of existing checker refinements improve
   separate direct-source records under the inherited compact contracts:

                               tokens   AST nodes   normalized bytes
   existing token record          241         267                566
   existing AST record            246         262                556
   checker_ast261.py              247         261                557
   existing byte record           272         306                469
   checker_bytes468.py            271         305                468

   The new checkers retain the existing guarded public calculus; they do
   not implement the new scalar constancy theory. No single program has
   the coordinatewise summary 241/261/468. The two candidates use different
   certificate framing. No token-record improvement is claimed.

The strongest requested target is not established: no globally simplest
axiomatization or single complete checker below every reported coordinate
has been proved. There is no matched complete-checker measurement for the
new scalar theory. The source corpus supplies exhibited size records, not
a general mathematical lower bound over every possible presentation.

COMPARISON SNAPSHOT

Repository: https://github.com/VladimirReshetnikov/ProveIt
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Pinned commit: 78edba03ee060644464f76e388578584b356520a

The read-only clone landed at 3fdd3af010e14bb3749cf71abc17a38d37de217b.
The docs, Artifacts, and README Git object IDs were checked unchanged.
The census includes all 19 incoming ZIP archives, including nested source
archives: 5,232 source occurrences, 1,881 distinct source contents, and zero
Python parse failures. The census alone does not certify every program's
semantics. Exclusions and exact archive hashes are in evidence/provenance.json.

RUNTIME AND METRIC

Measurements and executions used CPython 3.12.14.
Normalize each complete module by ast.unparse(ast.parse(source)) + "\n".
Count UTF-8 bytes of that normalized module; count all ast.walk nodes,
including operators and contexts; count tokenize tokens except comments,
indentation, line breaks, the encoding token, and the end marker.
No compressed payload or omitted acceptance component is credited.

INPUT CONTRACTS

These are compact acceptance modules, not fully validated JSON decoders.
The comparison assumes finite exact-integer/list certificate data and a
canonical closed guarded public Eq/D goal as specified in the paper.
Arbitrary native formulas need not have the ordinary public reading.

The AST candidate reads a JSON-lines proof stream; an unread suffix is
ignored. The byte candidate reads one JSON array and pops from its end.
Its final element is [A,0], using the shifted code; unused prefix data is
permitted. Successful acceptance is exactly the normal output ACCEPT
followed by a newline. The ideal mathematical correctness claims concern
finite recursions with unbounded resources. Real Python resource limits
can reject sufficiently large valid proofs.

REPRODUCTION

From the extracted package directory:

  python3 checkers/verify.py
  python3 mathematics/mathematical_checks.py
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

If latexmk is unavailable, run pdflatex with those flags three times.
The paper uses standard LaTeX packages and no external image assets.
The included Makefile provides the equivalent targets pdf and verify.

To try two positive fixtures directly:

  python3 checkers/code/checker_ast261.py < checkers/fixtures/ast/global_computation_zero.jsonl
  python3 checkers/code/checker_bytes468.py < checkers/fixtures/shifted_bytes/computation_zero.json

To repeat the full census against the pinned ProveIt tree:

  python3 evidence/census.py /path/to/ProveIt --output census_output

The census is read-only with respect to the source repository. It reports
an error instead of silently omitting ZIP nesting beyond its stated limit.

EVIDENCE AND LIMITATIONS

The checker receipt records exact source deltas, the metrics above, and
100 isolated executions in ordinary and optimized Python, with zero failed
expectations. Positive and negative certificates are included.

The mathematical receipt records finite checks of the predecessor, its
orbit invariant, successor comparison, and computation/equivariance in
the original three-copy model, including nested iterators. These finite
controls do not prove the infinite-model or bi-interpretation theorems.
The modified canonical-iterator model is supported by its written proof,
not by this finite receipt.

No new theorem or Python checker correctness proof was machine checked
in Lean or Rocq. The paper explicitly identifies inherited proof methods,
compiler lemmas, and checker techniques. It does not claim priority beyond
the inspected source corpus.

PACKAGE MAP

  report.pdf                      Compiled research paper
  report.tex                      Main LaTeX source
  mathematics/*.tex               Mathematical and implementation proofs
  mathematics/mathematical_checks.py
                                  Finite mathematical controls
  checkers/code/                  Two complete normalized candidates
  checkers/controls/              Exact existing sources and inherited proof
  checkers/fixtures/              Positive and negative certificates
  checkers/PROOF.txt              Detailed source-refinement correctness
  checkers/verify.py              Measurement and execution controls
  checkers/evidence/              Executed checker receipt
  evidence/claims.json            Explicit claim and limitation ledger
  evidence/provenance.json        Checker-source provenance and exclusions
  evidence/census.csv             Every inspected source occurrence
  evidence/census.py              Portable census script
  evidence/mathematical_receipt.json
                                  Executed finite mathematical receipt
  SHA256SUMS.txt                  Hashes of every other packaged file
  LICENSE.txt                     MIT-0 license; inherited terms preserved

The SHA256SUMS file excludes itself. Standard verification:

  sha256sum -c SHA256SUMS.txt

