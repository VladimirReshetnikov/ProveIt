# Polynomial shears and sign recovery for Diophantine consistency

Prepared for Vladimir Reshetnikov's ProveIt project, 23 October 2026.
Reviewed snapshot: `c1a102936aca437e9999530a0111e6ddab56dc6d`.

Read **report.pdf** or its editable source **report.tex**. The archive
contains nine completed fixed-coefficient equations and two improvements
to an alternative direct-certificate source. All coefficients needed to
define the completed equations are actual supplied integers.

## Completed equations

| Domain | Unknowns | Exact degree | Live binary operations / squared residuals | File |
|---|---:|---:|---|---|
| Unrestricted integers | 10 | 1,179,788 | 484 operations | `norm10/integer10_linear.json` |
| Unrestricted integers | 10 | 1,114,252 | 487 operations | `norm10/integer10_cubic.json` |
| Unrestricted integers | 10 | 1,081,125 | 521 operations | `norm10/integer10_sixterm.json` |
| Strictly positive integers | 11 | 211 | 112 operations | `positive11/p11_positive_degree211.json` |
| Unrestricted integers | 23 | 10 | 11 squared residuals | `integer/forms/centered23_degree10.json` |
| Unrestricted integers | 21 | 16 | 9 squared residuals | `integer/forms/pivot21_degree16.json` |
| Unrestricted integers | 20 | 20 | 8 squared residuals | `integer/forms/pivot20_degree20.json` |
| Unrestricted integers | 19 | 32 | 7 squared residuals | `integer/forms/pivot19_degree32.json` |
| Unrestricted integers | 18 | 88 | 6 squared residuals | `integer/forms/pivot18_degree88.json` |

The three ten-integer forms are triangular polynomial substitutions of
the incoming Round11 degree-1,245,324 / 480-operation equation. The
degree-1,114,252 choice gives a short seven-extra-operation improvement.
The degree-1,081,125 choice is proved optimal within the precisely defined
family of polynomial translations of the final coordinate with the norm
inputs fixed. This is not a global minimum claim.

The eleven-positive form improves the incoming degree-257 / 114-operation
equation in both measures. Its two-residual system uses 109 operations.
The integer family improves the strongest reviewed incoming forms at
several fixed variable counts, including degree 88 to 32 at 19 integers.

Every completed equation has a ZFC-formalizable existence equivalence with
the calibrated finite-refutation predicate, by composition with the named
inherited native/compiler/calculus theorem. Negation gives the requested
no-solution equivalence with Con(ZFC). No consistency assertion, globally
simplest equation, worldwide historical priority, or new end-to-end
Lean/Rocq/object-language ZFC certificate is claimed.

The ordinary K215 calibration proof is retained under `calibration/`;
it explicitly states the ZFC-provable halting/refutation equivalence.
The manuscript imports that ordinary theorem. It does not infer internal
ZFC provability from an external proof-assistant theorem or finite tests.

## What is new

- Short polynomial changes of the final norm coordinate cancel large
  leading squares while preserving the entire integer zero set.
- A positive auxiliary offset and two polynomial root centers recover
  the transport sign with a smaller weight; canonical completeness is
  proved explicitly.
- Two Pell root translations and a monic transport pivot are applied to
  the strongest incoming integer systems, with explicit inverse maps.
  The constituent transformations are credited to their existing sources.
- Natural-domain interpolation weights and deletion of identity steps
  improve a direct Horn-certificate source from 23 local witnesses at
  degree 14 to 21 at degree 14 or 22 at degree 12. These are local counts,
  excluding five exposed coordinates, not new global consistency equations.
- The quadratic graph `(n+b-p-1)^2+b*p=0` jointly represents natural
  predecessor and zero test; further exact local graph improvements follow.

## Reproduce

Python 3.10 or newer is suitable. The complete suite, including independent
symbolic audits, requires SymPy 1.14.0:

```sh
python3 -m pip install -r requirements.txt
python3 verify.py
python3 verify.py --optimized
```

Once the dependency is installed, verification is offline. The root
verifier works in an isolated temporary copy, so it does not modify the
delivered equations or receipts. Use `--output /path/to/receipt.json` to
save a fresh summary. The standard-library-only component checks can be
run separately; see each component's README. Acceptance checks do not
depend on removable Python assertions.

The supplied `VERIFICATION.json` records the release replay. Exact
algebraic checks establish polynomial identities; actual coefficient
bytes and nonzero leading coefficients establish the degree claims.
Finite evaluations are supplementary diagnostics, not proofs of the
unbounded compiler/refutation theorem.

Build the article with a standard TeX Live installation:

```sh
make pdf
```

The source uses ordinary LaTeX packages, listed in `report.tex`. The PDF
has been rendered and visually checked. Rebuilding a PDF is not expected
to preserve its bytes across TeX distributions.

## Contents and integration

- `report.tex`, `report.pdf`: complete mathematical article and future questions.
- `norm10/`: three literal graphs, full fixed payloads, root/defect certificates,
  builder, separate exact checks, and independent SymPy audit.
- `positive11/`: complete degree-211 graph, soundness/completeness proof,
  229-term degree certificate, native coefficient reconstruction and audits.
- `integer/`: five fully inlined residual packets, actual six-numeral binding,
  polynomial restoration maps, degree certificates, and independent checker.
- `alternative/`: two exact local selector polynomials and direct-checker
  graphs, including full sparse expansions and universal proofs.
- `calibration/`: the verbatim ordinary K215 calibration theorem and a
  source review distinguishing it from the unfinished object-calculus export.
- `PROVENANCE.json`, component source pins, `NOTICE.md`, licenses:
  immutable inputs and attribution.
- `MANIFEST.sha256`: release file hashes; the manifest excludes itself.

The wrapper can be placed in a new proposal subdirectory under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms`.
No proposal number is reserved. No existing repository package or branch
was edited or published. Keep each component's whole coefficient tuple
together; equal-looking port names across components are not interchangeable.
