# Fresh parameters from finite trees

This package contains a new structural representation of the existing native
iPRA calculus, plus three separate strict-checker refinements. It was prepared
against ProveIt commit `0198424b74acc33db20c5180c8019ecd7d14a75a`.
The initial structural controls were taken from the preceding commit
`fc05b10f0e03f22edbfdde9298a29fb2fee5dc59`; their contents are unchanged at the closing snapshot.

## Status of the requested target

**The requested construction below the global checker envelope was not found.**
The main result removes the global numerical scope counter by naming a fresh
parameter with a finite tree containing the current context, goal, and packet.
Proper-subtree size proves freshness; the opener leaves parameter names opaque.

The final main checker measures **246 tokens / 269 AST nodes / 546 normalized
bytes**, against **239 / 261 / 549** for its matched stream control. The current
compact envelope is **239 / 255 / 460**, attained by different programs and
interfaces. The main candidate saves three bytes against its matched control,
but is not below that global envelope.

The secondary fully validated profiles improve the strict envelope from
**302 / 340 / 584** to **299 / 335 / 583**, using three different programs and a
declared shifted encoding. No individual checker beats every old strict
coordinate. The strict programs are sound on accepted inputs and complete
for canonical theorem encodings; the broader accepted grammar includes aliases
for which completeness is not claimed. The repository documents the old
dummy-slot obstruction `[[5],[1]]`, shifted here to `[[7],[1]]`.
These finite-corpus records are achieved upper bounds, not proved
complexity lower bounds.

## Contents

- `structural_parameters.tex` and `structural_parameters.pdf`: full report,
  explicit calculus, representation, written correctness arguments, inherited
  bi-interpretation, measurements, limitations, and further research questions.
- `structural/checker_opaque_stream.py`: the complete measured compact checker.
- `structural/reference_checker.py`: readable checker with explicit validation
  of consumed integer/list data and closed canonical guarded public goals.
- `structural/translate.py`: untrusted paired fixture translator; not part of
  either checker and not a theorem about arbitrary old raw certificates.
- `structural/fixtures/`: eight accepted proof streams, including a five-packet
  public quantified example and a 281-packet guarded induction proof.
- `structural/negative/`: rejected certificates and a deliberately unsound
  fixed-name mutant used ONLY to demonstrate a concrete capture attack.
- `structural/controls/`, `structural/source_fixtures/`, and `reference/`:
  frozen comparison sources, fixtures, and upstream license.
- `strict/`: three standalone strict checkers, exact pinned controls, shifted
  syntax specification, correctness note, examples, and verification scripts.
- `run_checks.py`, `results.json`, and the per-suite receipts: reproduction and
  finite executable evidence. Source hashes are recorded in the measurements.
- `CLAIMS.json` and `SOURCES.json`: machine-readable claim boundaries and provenance.

## Reproduction

Exact source-size measurements use CPython 3.12.14. The programs require only
the Python standard library. From this directory:

```bash
python3 run_checks.py
python3 structural/checker_opaque_stream.py < structural/fixtures/quantified_reflexivity.jsonl
python3 structural/reference_checker.py < structural/fixtures/quantified_reflexivity.jsonl
python3 strict/checkers/strict_bytes583.py < strict/examples/four_zero.json
pdflatex -halt-on-error structural_parameters.tex
pdflatex -halt-on-error structural_parameters.tex
```

The source uses conventional LaTeX packages, including amsmath, amssymb,
amsthm, mathtools, microtype, listings, xurl, and hyperref. The TeX source is standalone and includes the exact checker listing.

## Meaning of the new names

For context `g`, goal `a`, and packet `[s,u,t]`, the fresh token is
`[s,u,t,g,a]`. It is larger than every old token occurring in those data.
Arrays with at least four children are opaque variable names at term positions;
their entire finite trees identify the variables. At formula positions they
retain a neutral truth reading. Negative scalar leaves no longer name variables.
The new decoder is not interchangeable with the old decoder on arbitrary raw
certificates. Canonical closed public goals retain their old encoding.

The names are proof syntax, not a new arithmetic domain. The arithmetic basis,
the native logical translations, and the whole-domain identity bi-interpretation
with full first-order iPRA are inherited from the pinned ProveIt development.
The new contribution is the representation and its local freshness proof.

## Limits

- The compact module has a declared canonical public-goal/integer-list input
  contract. It is not a strict arbitrary-JSON frontend. Use the readable checker
  for the explicitly validated interface, and count that entire file if measuring it.
- Parameter trees can enlarge certificates substantially: the tested induction
  example grows from 12,726 to 635,588 JSON-line bytes.
- Correctness has a written mathematical argument. Tests support implementation
  behavior; they are not a Lean or Rocq formalization of Python execution.
- No claim of a globally simplest axiomatization or a proven checker-size lower
  bound is made. No new primitive-recursion or logical axiom is deleted.

Original code and adapted controls are covered by the included MIT No Attribution
license. The complete report identifies the inherited results and the new work.
