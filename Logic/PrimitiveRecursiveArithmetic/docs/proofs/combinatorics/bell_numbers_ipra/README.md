# Bell numbers in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, November 15, 2026.

Start with `paper/bell_ipra.pdf`. Its source is `paper/bell_ipra.tex`, which
includes the numbered section files in the same directory. The report gives
human-readable proofs and an explicit arithmetic interpretation of the
analytic statements, followed by the Lean formalization plan.

## Main mathematical results

The report covers the principal Bell-number statements on the requested
MathWorld and Wikipedia pages: finite identities and interpretations,
Dobiński and Comtet formulas, generating functions and integral
representations, both logarithmic inequalities, Hankel determinants,
Touchard congruences and constructive modular periods, the all-n bound with
constant 0.792, the de Bruijn expansion, the Lambert W equivalents, and the
two-correction Moser–Wyman expansion under logarithmic shifts.

The growth estimates include explicit remainders. In particular the
Wikipedia leading equivalent has relative error at most 1/q once
n >= 2^(64 q^2). The constants are deliberately generous: they supply
primitive recursive moduli and are not recommended for numerical computation.

The reading guide records the precise coverage and exclusions. Open
conjectures and large Bell-prime computations are not claimed as proofs.

## Formal status

`lean/BellCore.lean` is compiled under Lean 4.32.0 with Std only. It proves a
finite core: Stirling boundary equations, the weighted Bell recurrence,
positivity, monotonicity, B_(n+1) <= (n+1) B_n, B_n <= n!, and values through
B_10. `verification/lean-axioms.txt` contains the axiom audit.

`lean/BellTargets.lean` supplies executable rational approximants, a packed
first-order Bell program, and precise propositions for the remaining work.
Names ending in `Target` are unproved proposition definitions, not axioms
or completed theorems. No source uses `sorry` as a proof.

The general analytic results and the compilation to ProveIt's object-language
`Prf PRAAx` remain formalization work. The human proofs, bounds, encodings,
and dependency order are supplied in the report. Ambient Lean theorems are
not silently equated with iPRA derivations.

## Reproduce

Requirements: Python 3.10+ (standard library only), Lean 4.32.0, and a normal
LaTeX installation with pdfLaTeX and the standard packages listed in the main
TeX source. `lean/check.sh` also uses ripgrep for its error scan.

```sh
python3 code/verify_bound.py
python3 code/verify_finite.py
python3 code/verify_numeric.py
bash lean/check.sh
bash build_pdf.sh
```

Set `LEAN_BIN=/absolute/path/to/lean` if Lean is not on PATH. The Lean scripts
write reproducible compiler outputs to `lean/build/`, which is excluded from
the delivery archive. The numerical scripts regenerate their JSON/CSV
certificates in `code/`.

`verify_bound.py` certifies all 511 small cases of the 0.792 bound using
integer comparisons and rational upper bounds for logarithms. Its result is
part of the finite computation proof; the report handles every n >= 512.
The finite diagnostic script checks selected instances of universally proved
identities and complete finite bijections. It also certifies the listed
least periods for moduli 1 through 12. Neither Python script is a syntactic
iPRA proof checker. `verify_numeric.py` certifies the listed digit counts
and the small primality data by integer arithmetic.

## Repository snapshot

The inspected ProveIt snapshot is
`c0d0dc37f60aea10c0182ba4eece9eae8c7e13c6`. The exact inspected paths and Git
blob identifiers are in `reference/proveit_audit.json`. No change to the
remote repository is part of this package.

## Files

- `paper/`: the complete report, PDF, and all LaTeX sources.
- `lean/`: compiled source suite, target definitions, and build instructions.
- `code/`: exact certificate generators and their compact output data.
- `reference/`: pinned repository audit.
- `verification/`: Lean axiom report and delivery validation summary.
- `MANIFEST.sha256`: checksums of the delivered files other than the manifest.

The report's references identify the requested source pages and relevant
primary papers. The proofs and explicit estimates in the report are
developed there rather than imported as unproved assumptions.
