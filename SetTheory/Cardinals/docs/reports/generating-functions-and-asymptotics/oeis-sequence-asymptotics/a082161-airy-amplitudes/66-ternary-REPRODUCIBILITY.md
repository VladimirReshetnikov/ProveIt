# Reproducibility

Run `bash replay.sh /an/empty/writable/output-directory` from this package. The default output is `output/replay/`. Payload files are not overwritten. The replay:

1. Checks the exact transformed three-step recurrence
2. Checks critical and moving weighted boundary and energy identities with rational arithmetic
3. Checks completed-run DFA counts, finite-level/time truncation indices, and backward bridge monotonicity exactly
4. Recomputes polynomial–Airy corrections in two independent symbolic implementations and compares the exact saved results
5. Runs floating-point diagnostics for the two quasimode residual orders and inverse corrections
6. Rebuilds the supplied TeX from a fresh directory, checks layout/reference warnings, and extracts the PDF text

Dependencies: Python 3 with SymPy, SciPy and mpmath; a TeX distribution providing pdfLaTeX and the standard packages loaded in the source; Poppler utilities. Exact recurrence and boundary checks use only Python's standard library. No network access is needed for replay.

The PDF build helper creates missing format files and font maps only in its writable build directory, using the installed TeX distribution. It does not require writing into a system TeX tree. On a minimal installation the first build can be slower.

Exact arithmetic is used for enumerative and algebraic checks. Floating diagnostics do not replace the analytic proofs. PDF byte identity is not promised across TeX installations; the source, text, formulas, and build warnings are the reproducibility targets.

`SHA256SUMS` identifies the frozen payloads. Generated replay outputs are excluded from that manifest and from the release archive.
