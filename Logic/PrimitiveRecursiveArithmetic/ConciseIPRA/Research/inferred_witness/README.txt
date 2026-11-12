iPRA WITH INFERRED WITNESSES
Research note prepared for Vladimir Reshetnikov, 11 November 2026

START HERE

Read report.pdf (18 pages). Its complete LaTeX source is report.tex together
with theory/*.tex, evidence/*.tex, and code/checker.normalized.py.

The new mathematical ingredient is a deterministic opening rule for the
paired binder D[x,y] B = exists x (B(x,0) -> forall y B(x,y)). For a fresh
parameter b, if the canonical zero instance is literally 0=0 and the
canonical unit instance is literally b=r, the rule opens the specialized
clause B(r,0) -> forall y B(r,y). Otherwise it opens at b. The term r may
contain b; substitution is simultaneous and is performed once. The branch
conclusion must be free of b in either case.

This removes a supplied replacement term and an equality-proof premise
from the closest incoming witness-discharge proposal. A written universal
proof recovers ordinary elimination, arbitrary equality transport, and
exactly the inherited canonical clause consequence relation. Composing
with the inherited arithmetic bridge gives bi-interpretability with full
first-order intuitionistic primitive recursive arithmetic, with whole
numerical domains, actual equality, and identity numerical composites.

WHAT SIMPLER MEANS

The calculus has one fixed reflexivity clause and three inference families:
clause use, paired introduction, and opening with an inferred witness.
The incoming witness-discharge proposal already had three families. The
new reduction is in the interface of the third rule, not in that count.

The complete strict checker is 1,990 normalized Python source bytes versus
2,273 for the incoming witness-discharge checker. It includes normalization,
syntax, binding, scope, proof inference, and the JSON interface. The new
implementation also infers proof conclusions, so the full source saving is
not attributed solely to the mathematical reduction. Matched controls are
included: explicit equality at opening takes 1,998 bytes, and explicit
equality at output takes 1,983 bytes. Token and AST comparisons are mixed.
The repository's 516-byte compact codec and 788-byte validated-public-goal
record remain shorter. No absolute minimality theorem is claimed.

PROOF AND VERIFICATION STATUS

The new equivalence is a mathematical proof, with a separate review and
independently written finite implementation checks. It is not newly
formalized in Lean. The two copied Lean modules document the inherited
bridge and require the upstream project for their imports; they do not
constitute a standalone formalization of this new opening rule.

Recorded validation, under Python 3.12.14:
  - 12 accepted closed proof certificates;
  - 38 rejected adversarial inputs;
  - 114 normal/optimized-Python command-line checks;
  - 12 exact translations to the matched explicit-equality control;
  - 24 exact-fuel and one-less-than-required checks;
  - a regression where substitution creates the naming guard;
  - 6,292 independent syntax, scope, substitution, and semantic checks,
    with zero failures.

These executions are finite implementation evidence. They are not a
consistency proof and do not replace the universal mathematical argument.

REPRODUCE

From this directory, with Python 3.10 or newer (measured with 3.12.14):

    python3 reproduce.py

This uses only the Python standard library, runs both validation suites,
and regenerates evidence/comparison.json, comparison.csv, the TeX table,
and the summary files. Source-format metrics may change between Python
versions because ast.unparse is part of the measurement convention.
Recorded path fields will change after extracting the archive elsewhere.
Reproduction overwrites generated evidence, so it also changes the initial
file manifest; MANIFEST.json describes the delivered snapshot.

To check one certificate directly:

    python3 code/checker.py < code/examples/reflexivity.json

For the certificate format, including exact scope and typing conventions,
read code/FORMAT.txt. The proof builders and test scripts are untrusted:
acceptance depends only on the complete checker being invoked.

To rebuild the PDF using an installed TeX distribution:

    python3 build_pdf.py

The build script needs pdfTeX, kpsewhich, Latin Modern, AMS fonts, and the
LaTeX packages listed in report.tex. It uses latexmk when available and
otherwise runs pdflatex three times. For a TeX installation containing
sources but missing generated formats/font maps, it creates local support
files in a temporary directory. It performs no downloads or system edits.

On a normally configured TeX installation, this is also sufficient:

    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

PACKAGE MAP

  report.pdf / report.tex       The mathematical report and main source.
  theory/opening_discharge.tex  New calculus, substitution, and equivalence.
  theory/normalization.tex      Canonical syntax metatheory.
  theory/bridge.tex             Arithmetic and both interpretation composites.
  theory/implementation.tex     Complete-checker interface, metrics, limits.
  code/checker.py               Selected strict checker (1,990 bytes).
  code/checker_fuel.py          Explicitly fuel-bounded checker.
  code/control*.py              Matched explicit-equality opening controls.
  code/output_*.py              Alternate output-discharge comparisons.
  code/examples/               Accepted certificates.
  code/reject_examples/        Rejected adversarial certificates.
  code/control_examples/       Translated explicit-equality certificates.
  code/fuel_examples/          Certificates with exact checked fuel.
  code/independent_validation.py
                               Independent parser/normalizer and checks.
  evidence/                    Measurements, executions, audit, PDF checks.
  reference/                   Attributed inherited proofs and source snapshots.
  reference/optional_output_discharge.tex
                               New alternate output variant, not the main rule.
  reproduce.py / build_pdf.py  Reproduction entry points.
  CLAIMS.json                  New, inherited, tested, and unclaimed statements.
  PROVENANCE.json              Pinned upstream paths and source hashes.
  MANIFEST.json                SHA-256 of every delivered file except itself.
  LICENSE-upstream.txt         The upstream MIT-0 license.

PINNED BASELINE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 17898ea7e6a1300dfdcad71040d5daeed67916d4
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The audit covered the README's 67 filed packages and all six incoming ZIP
packages, including ipra_witness_discharge_2026-11-11.zip. The evidence
inventory records their contents. PROVENANCE.json records which snapshots
are reproduced, which components are inherited, and which are new work.
