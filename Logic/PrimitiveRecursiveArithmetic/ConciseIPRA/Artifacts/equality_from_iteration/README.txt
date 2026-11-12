EQUALITY FROM ITERATION
A smaller iPRA presentation and a uniform evaluation companion
Prepared for Vladimir Reshetnikov, November 11, 2026

RESULT

The main raw calculus deletes the direct equality-composition case from
the current computational_equality proposal. The zero-iteration case
already derives it through an identity frame. Every open sequent is
preserved on exactly the same syntax, so the existing full bi-interpretation
with iPRA transfers unchanged.

A companion calculus makes zero iteration definitional and uses only
reflexivity and one successor-evaluation schema for arithmetic and equality.
With Hyp, QE, DE and the inherited witness-directed DI, it has six displayed
rules. DI still has its explicitly stated syntax-directed mode test.

MAIN FILES

report.pdf              Complete paper, including all axioms/rules, proofs,
                        comparisons, limitations and further research questions.
report.tex              LaTeX source for the paper.
code/raw_two_case.py    Selected standalone raw checker (recommended for
                        the strict matched implementation improvement).
code/checker.py         Standalone zero-normal companion checker.
code/raw_control.py    Byte-identical upstream raw baseline.
code/normalized_control.py
                        Matched canonical control retaining the root case.
code/translate.py      Compilers eliminating root Eval within each fixed
                        syntax interface; NOT a raw-to-canonical compiler.
code/FORMAT.txt        Exact certificate format and implementation invariants.
code/verify.py         Reproducible measurements and finite verification.
code/certificates/     62 checked positive certificates.
code/upstream_examples/
                        14 original source examples used in the comparison.
evidence/              Measurements, verification log, source provenance.
reference/lean/        40 frozen upstream Lean modules (reference sources).
reference/bridge/      Five inherited mathematical bridge components and
                        upstream licence. These are inclusion fragments.
reference/*_report.tex Frozen comparison reports, supplied for reference;
                        they are not independent build targets here.
LICENSE-upstream.txt   Licence accompanying inherited source material.
MANIFEST.json          SHA-256 checksums of the delivered files.

MATCHED METRICS

CPython 3.12.14; ast.unparse plus one final newline; gzip level 9, timestamp 0.

Module                       Tokens   AST nodes   Bytes   Gzip-9
Upstream raw                     959        1026    3039      966
Raw two-case (main)              954        1019    2996      955
Canonical with root              987        1059    3064      982
Canonical single evaluation     979        1047    3011      965

The raw reduction strictly improves all three source-size coordinates in
the unchanged strict interface. The canonical companion has a simpler
arithmetic rule, but does not dominate the raw checker in these metrics.
No absolute simplicity minimum or new global compact-codec record is claimed.

REPRODUCE

From this directory:

  python3 reproduce.py

This needs Python 3.10 or later, no network and no third-party Python package.
Exact published measurements are pinned to CPython 3.12.14. Other interpreter
versions may produce different normalized source or compressed byte counts.
The standalone checkers reject invalid certificates without relying on assert.

Check one certificate:

  python3 code/raw_two_case.py < code/certificates/raw/root_bootstrap_open.json
  python3 code/checker.py < code/certificates/normalized/used_induction_hypothesis.json

Rebuild the paper (normal LaTeX packages are required):

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

VERIFICATION

The delivered verification passed 460 standalone process checks in ordinary
and optimized modes, all 62 end-sequent translation checks, 1280 structural
normalization checks and 320 independent numerical substitution checks.
There were zero unexpected outcomes. These finite checks do not establish
the universal theorems; the report supplies mathematical proofs.

The new reductions and Python checkers have not been formalized or compiled
in Lean or Rocq. The upstream Lean sources document the inherited native/
iPRA and zero-normalization bridges. They were fetched and checked against
Git blob hashes, but were not rebuilt in this environment.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: fa9d969919315b97796a1dd288f431cd3e41ffca
Project: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Raw baseline Git blob: fb0c113d07d3d25632e8c077f91268f089f71bf3

Every inherited file's path, pinned URL and Git blob identity are recorded
in evidence/source_provenance.json. The archive makes no changes to the
upstream repository.
