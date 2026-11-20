# Verification evidence

- `lean-build-and-axioms.log`: successful Lean 4.19.0 build, all 31 named
  theorem dependency reports and six proof-bearing definition reports;
  the 12 examples also completed successfully.
- `python-tests.log`: all 16 reference-algorithm tests passed.
- `circuit-demo.json`: executable example from the finite compiler.
- `latex-build.log`: final successful LaTeX pass.
- `pdfinfo.txt`: final PDF metadata and page count.
- `pdf-validation.json`: final text, font, link, and geometric checks.
- `visual-review.md`: review of all rendered PDF pages.
- `upstream-sources.json`: pinned repository paths, Git blob hashes and URLs.

The independent Lean companion proves semantic finite mathematics. It does
not certify that the major complexity theorems have already been translated
to the object theory's `Prf PRAAx` judgment. Finite Python checks are not
mathematical proofs or machine resource certifications.
