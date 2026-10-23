# Repository integration

This package is a new research supplement for the collection at:

`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`

It was reviewed against ProveIt commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`. No repository files were modified
or published during preparation. The folder can be placed as a new numbered
supplement using the repository's intake convention; no ordinal is reserved
by this archive.

## Suggested collection entry

**Direct quadratic coding for ZFC consistency** — ten unrestricted integer
unknowns; one equation of exact total degree **267,823,432**, evaluated in
**786** binary arithmetic operations (539 multiplication, 222 addition,
25 subtraction), with 17 nonliteral fixed leaves. Direct simultaneous
quadratic coding replaces the quartic/base-5 source in package 31. The
principal instance retains all four package-31 coefficient ports. A second
fully bound instance incorporates an exact bounded-checksum compiler with
native base **2^590069**, largest native port **592,884 bits**, and
**295,388 raw bytes** across all four ports. Both have separate generators,
bindings, exact-degree certificates and independent audits.

## Review entry points

- `report.tex` and `report.pdf`: complete article and equations.
- `DIRECT_QUADRATIC_PROOF.md`: proof of the changed source interface.
- `generated/direct10.json`: principal literal circuit.
- `optional_compact/generated/direct10_compact.json`: separately rebound
  compact circuit.
- `optional_compact/coefficients/PROOF.md`: complete new compiler adapter.
- `reproduce.py`: one command for both complete instances.
- `verification/`: principal finite certificates and independent audit.
- `optional_compact/verification/`: compact certificates and independent audit.
- `review/COMPARISON_AT_PIN.md`: immutable copy of the reviewed collection.
- `PROVENANCE.json` and `data/UPSTREAM_FILES.json`: pinning and inherited sources.
- `MANIFEST.sha256`: delivery hashes; not a mathematical proof certificate.

All active code paths are relative to the package. Python 3.11+ and its
standard library suffice for the finite checks; no network, SAT solver,
symbolic-algebra installation or proof search is needed. The article
requires a standard pdfLaTeX installation with common AMS, Latin Modern,
microtype, geometry, hyperref and table packages.

Inherited source documents retain their original references and context.
Their historical relative links are not runtime dependencies. Original
licenses and notices are retained. New code and prose use the MIT-0 terms
in `LICENSE`.

## Mathematical scope

The main improvement is established by an ordinary proof formalizable in
ZFC, composed with the inherited native compiler/K215 calibration and Sun's
2021/2026 Lucas results. The finalizer is unchanged after substituting its
source inputs. Finite audits prove the stated algebraic and literal-data
facts; sampled modular evaluations serve only as transcription checks.
No new end-to-end Lean/Rocq certificate or consistency proof is claimed.
The ten-variable count, degree and circuit size are not claimed optimal.
