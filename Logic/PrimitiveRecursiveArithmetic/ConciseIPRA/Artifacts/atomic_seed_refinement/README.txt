iPRA: ATOMIC ZERO CONTRACTION AND VERIFIED CHECKER REFINEMENTS
============================================================
Prepared for Vladimir Reshetnikov, 12 November 2026.

OUTCOME

The requested construction below the entire current checker-size frontier
has NOT been established. This archive contains two precise results:

1. A six-family presentation using atomic-seed zero contraction and raw rule
   metadata, with a written proof of full consequence equivalence to the native
   scalar core and hence its inherited bi-interpretation with first-order iPRA.

2. Two exact implementation refinements of the existing native checkers.
   These programs implement the inherited calculus, NOT the new atomic-seed
   calculus. Each preserves its own predecessor's raw JSON acceptance relation.

Complete-module metrics (CPython 3.12.14, ast.unparse + one LF):

                                       Tokens     AST     Bytes
  Native public-goal predecessor           327     375       643
  New public-goal checker                  326     370       636
  Native alphabet-and-goal predecessor     344     392       637
  New alphabet-and-goal checker            341     387       628

The first pair validates the native public goal. The second also imposes
the whole-certificate integer/list alphabet gate. These validation boundaries
are different; each reported improvement is against its EXACT predecessor.

The current compact guarded incumbents attain (248 tokens, 270 AST nodes,
479 bytes), in different programs with their documented interfaces. They
remain smaller than the delivered construction. These are observed minima,
not proved absolute lower bounds.

MATHEMATICAL PRESENTATION

Terms: variables, 0, successor, I(n,a;u.h), binding u only in h.
Formulas: equality, Q_y B, D_{x,y} B.

The partial normalizer recursively contracts I(0,a;u.h) only when the
NORMALIZED initializer a is a variable or literal zero. Six rule families:
Hyp, successor computation IS, crossed one-term transport Tr, closure
specialization QE, witness discharge DE, and one introduction DI.

Every rule retains its RAW body/template metadata and normalizes the whole
schema instance only AFTER its raw capture-avoiding substitutions. DI selects
progress exactly for an equation matrix and RAW witness literal zero;
otherwise it selects cases. Freshness and type checks cover the raw metadata.

The key derived zero-computation proof uses the raw QE body
  B(y) = (I(0,y;u.h)=y).
Its normalized closure is Q_y(y=y), its normalized zero instance is 0=0,
and specialization at arbitrary t gives N(I(0,t;u.h)=t).

The normalizer DOES NOT commute with substituting into an already normalized
body. This fact and the required raw metadata are explicit in the paper,
the reference checker, and the rejecting certificate suite.

The new complete tagged checker is larger than its matched seven-family raw
control: 1333/1521/5373 versus 1319/1507/5348. Removing a rule family therefore
has not produced the requested implementation-size reduction.

FILES

report.tex, report.pdf
    Main research report, including exact axioms/rules, mathematical proofs,
    bi-interpretation composition, measurements, provenance and limitations.
proofs/atomic_seed_section.tex
    Complete new mathematical section, included by report.tex.
code/native_goal_checker.py
    Complete exact 326-token / 636-byte public-goal-validating native checker.
code/native_strict_checker.py
    Complete exact 628-byte alphabet-and-public-goal-validating native checker.
code/atomic_seed_checker.py
    Standalone strict tagged checker of the six-family new presentation.
code/rebasing_counterexample.py
    Independent finite evaluation of a dangerous naive arity-code contraction.
code/ATOMIC_CHECKER_README.txt
    Tagged language and certificate protocol.
reference/
    Frozen matched controls, selected compact incumbents, and inherited proof
    source chapters. The source chapters belong to the upstream unified article
    and are not standalone PDFs; report.tex is the standalone build target.
tests/native/, tests/certificates/, tests/atomic_cases.json
    Frozen positive and negative certificate fixtures.
tests/make_atomic_certificates.py
    Untrusted atomic-certificate producer. The checkers independently replay
    every positive certificate; the producer is not part of the trusted kernel.
evidence/
    Exact source metrics and hashes, incoming-archive census, provenance,
    and verification receipts.
proofs/PARITY_PROOF.txt, proofs/ATOMIC_THEORY_REVIEW.txt
    Detailed checker-equivalence argument and independent mathematical review.

Run all reproduction commands from this archive's root.

REPRODUCTION

  python3 verify_manifest.py
  python3 measure.py
  python3 verify_parity.py
  python3 verify_atomic_seed.py
  python3 code/rebasing_counterexample.py
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The Python commands need only the standard library. The PDF build needs a
working pdfLaTeX installation and the packages listed in report.tex.
For certificate regeneration: python3 tests/make_atomic_certificates.py
The checkers do not invoke that producer. Check the manifest BEFORE rebuilding
or regenerating files, because PDF metadata and receipt metadata may change.

TEST RECEIPTS

The parity refinements: 56 cases, two matched predecessor/candidate pairs,
ordinary and -O Python, 448 process executions, zero mismatches.
The atomic presentation: 20 persisted cases plus malformed-data and matched
control checks, 54 executions, zero failed expectations. An induction proof
actually uses its induction hypothesis. A raw-zero-alias case-introduction
proof is accepted, while the same branch with a literal-zero witness rejects.

Finite testing is implementation evidence. Universal mathematical claims rest
on the written proofs, including the inherited native/iPRA bridge. No new
Lean or Rocq formalization and no absolute minimality theorem are claimed.

PINNED SOURCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: dbe0094df420f93f2d5be366b94a0d0c4318dc5b
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The review includes all six then-current docs/incoming ZIP archives.
See evidence/incoming_archive_manifest.json for their exact hashes.

The presentation developed here is compared with the relevant inherited
normalization frameworks; no historical priority claim is made.
Original source license: LICENSE.txt (MIT No Attribution).
