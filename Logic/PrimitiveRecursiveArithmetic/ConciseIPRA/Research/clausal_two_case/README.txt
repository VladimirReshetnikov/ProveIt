A SMALLER RAW CLAUSAL PRESENTATION OF iPRA
========================================

Comparison commit: 5d85023b0688e03b75f0ec3a04bb43ef0bb51705
Date: November 11, 2026 (Pacific time)

RESULT

The five-pattern raw clausal calculus in ConciseIPRA is simplified by
deleting the root case of computational equality. Terms, formulas,
clauses, and ordinary substitution remain unchanged. The new system
uses only reflexivity, two-case Eval, clause Use, paired elimination,
and witness-directed paired introduction.

Every sequent of the existing raw clausal theory is preserved. A removed
root step p:s=t, q:s=r is replaced by

    Eval0(p, Eval0(q, Refl(I(0,s;u.0)))) : r=t.

The two premise proofs each occur once. With k removed root steps, a
proof of N nodes becomes one of exactly N+2k nodes. Composing the
identity comparison with the existing native/iPRA bridge gives full
first-order bi-interpretability, whole numerical domains, actual
equality, both numerical composite graphs x=y, and equiconsistency.

The identity-frame reduction and the clause presentation were already
proved separately in the repository. This package combines them and
supplies measured complete checkers and checked certificate translations.
It is an incremental simplification, not an absolute-minimality result
or a new arithmetic-strength theorem. It does not beat the historical
approximately 516-byte compact-envelope checker family.

MAIN DELIVERABLES

  report.pdf / report.tex      Full paper: complete theory, proofs,
                              both interpretation composites, metrics,
                              scope invariant, and full checker listing.
  code/checker.py              New complete readable strict verifier.
  code/control_three_case.py   Matched control, with the removed row.
  code/compile_proof.py        Untrusted source-to-target translator.
  code/verify.py               Readable-checker tests and measurements.
  examples/                   Five nontrivial accepted certificates.
  comparison/                 Literal upstream deletion, portable tests,
                              47 translated proofs, negative corpus,
                              exact N+2k translation checks.
  reference/                  Pinned upstream source excerpts, original
                              control modules, and mathematical bridge.
  evidence/                   Source hashes, metrics, validation logs,
                              independent scope review, and PDF review.
  CLAIMS.json                 Machine-readable claim boundaries.
  reproduce.py                Single reproduction entry point.

RUN

Python 3.10+ supports the match syntax. Measurements were taken using
CPython 3.12.14. There are no third-party Python dependencies.

    python3 code/checker.py < examples/used_induction_hypothesis.json
    python3 reproduce.py

Translate an old raw_clausal certificate, checking the result:

    python3 code/compile_proof.py --legacy < old.json > translated.json
    python3 code/checker.py < translated.json

To regenerate the PDF as well (a TeX installation with the packages
listed in report.tex is required):

    python3 reproduce.py --pdf

The verifier accepts exactly a JSON object with goal and proof fields.
Its public interface checks closed theorems; it checks local hypotheses
and eigenvariables inside proof branches. The paper gives the complete
syntax and packet format. The comparison/ verifier has the original
compact raw-term format; use its own certificates with that verifier.

MEASUREMENTS

Complete program                       Bytes  Tokens  AST  Gzip-9
Pinned raw-clausal checker              3046     853   993     990
Literal root-row deletion               2999     848   986     979
New matched three-case control          2861     808   888     985
New two-case checker                    2787     794   868     972

Bytes are UTF-8 bytes after removing the leading module docstring and
applying ast.unparse plus one final newline. Layout/comments are not
significant tokens. Gzip uses level 9, mtime=0, and is informational.
Both measured complete sources and their .gz files are included.
The 259-byte reduction from the upstream readable module combines the
mathematical deletion with a shared syntax traversal and inferred
elimination conclusions; the direct 47-byte comparison isolates the
mathematical deletion.

VALIDATION AND LIMITATIONS

The direct-deletion suite passes 47 translated closed proofs, 28
rejection cases, 5 obsolete-certificate checks, 6 open-context checks,
and 320 CLI runs. It removes 61 root nodes and verifies N+2k at every
transformed subtree. The new readable checker passes 32 positive and
29 rejection examples, 122 CLI runs, and 1000 deterministic substitution
comparisons. The suites overlap. Normal and python -O execution are
checked, because production acceptance does not rely on assertions.

The universal equivalence and bi-interpretation arguments are written
mathematical proofs. No new Lean/Rocq formalization of this clausal
calculus or Python verifier is claimed. Included Lean source excerpts
identify the inherited bridge; they are not a standalone Lean project
and were not compiled here. Finite tests do not replace those proofs.
Like any finite implementation, Python can reject very deep valid
certificates because of recursion or memory limits.

The entire package is supplied under LICENSE.txt. Upstream source
copies are identified by exact pinned URLs and verified Git blob hashes
in evidence/source_manifest.json. No repository changes are required
to use this package.
