# Direct closure induction for iPRA

This package gives a modest simplification of the current ConciseIPRA
primitive interface: equation induction introduces `Q_y E(y)` directly,
without an existential witness. The numerical language, formula meanings,
entire consequence relation, whole-domain bi-interpretation with iPRA,
and equiconsistency remain unchanged.

**The 529-byte compact-checker frontier is not improved.** The controlled,
explicit checker comparison saves 83 normalized bytes, 18 significant tokens,
and 21 AST nodes. The primitive rule count remains eight. The direct-Q rule
was already derived in the repository; the new choice is to make it primitive.
This is not a claim of a globally simplest axiomatization or a new arithmetic
foundation.

## Contents

- `ipra_direct_closure.pdf` and `report.tex`: the report, complete axioms and
  rules, exact equivalence proof, both interpretation composites, measurements,
  implementation correctness arguments, and attributed arithmetic appendices.
- `ipra_direct_closure.tex`: standalone expanded LaTeX source, including the
  inherited mathematical appendices and full strict checker listing.
- `code/strict_q.py`: complete standalone strict checker for the new rules.
- `code/strict_old.py`: matched standalone checker for the old rules.
- `code/translate.py`: untrusted proof producers translating both ways.
- `code/build_strict_checkers.py`: recreates the two standalone checkers from
  a shared body and their two different progression fragments.
- `tests/`: positive, negative, scoping, translation and round-trip tests,
  including actual JSON proof certificates.
- `measure.py`, `evidence/measurements.json`, and `evidence/gzip/`: exact
  source metrics, hashes, and gzip-9 artifacts for both raw and normalized code.
- `lean/closure_progress.patch`: an uncompiled migration proposal, with
  applicability evidence and an explicit description of its limitations.
- `reference/`: pinned inherited source excerpts, mathematical dependencies,
  selected compact checkers, and the repository license.
- `experiments/counter_vectors/`: a separately validated 533-byte protocol
  that removes zero-predecessor repair at a four-byte source cost. Its
  528-byte rejected variant is included only to reproduce a completeness gap.

## Reproduce

From this extracted directory:

```sh
python3 reproduce.py
python3 code/strict_q.py < tests/certificates/q_equation_induction_q.json
python3 code/translate.py q-to-old < tests/certificates/q_equation_induction_q.json > translated.json
python3 code/strict_old.py < translated.json
```

Every checker prints `ACCEPT` only after validating the full certificate.
The producers are not trusted dependencies. None of the programs uses
`eval`, `exec`, certificate imports, or assertions for its acceptance checks.
The suites also run the public checkers with `python -O`.

Python's standard library is sufficient. The recorded metrics use CPython
3.12.14 and zlib 1.3.2. Other versions may change normalization or gzip sizes.

Build the PDF with an ordinary configured TeX installation:

```sh
python3 build_report.py
pdflatex -interaction=nonstopmode -halt-on-error ipra_direct_closure.tex
pdflatex -interaction=nonstopmode -halt-on-error ipra_direct_closure.tex
```

The expanded file is self-contained. `report.tex` instead uses the included
reference fragments and checker listing. A PDF build does not run Lean.

## Proof and verification status

The two presentations are proved to derive exactly the same native sequents.
The inherited iPRA interpretations therefore transfer, with actual equality
and the identity graph on each whole numerical domain. Proof translation
adds exactly two old-calculus nodes per new Q-induction node, or three
new-calculus nodes per old D-progression node.

The Python programs have written structural soundness/completeness arguments
and executable regression evidence. These are not Lean/Rocq certifications.
The Lean patch passed `git apply --check` against pinned sources but was not
compiled. Do not treat patch applicability as kernel verification.

The comparison commit is
`b17dd5487f34adea473a0204c5320fb3eeb8910e`, under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA` in
<https://github.com/VladimirReshetnikov/ProveIt>.
The precise source provenance is in `evidence/source_snapshot.json`.
No GitHub files were changed or published by this investigation.
