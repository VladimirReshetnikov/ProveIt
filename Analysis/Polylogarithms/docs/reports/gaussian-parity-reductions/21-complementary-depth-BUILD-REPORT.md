# Build and verification record

The delivered article was compiled with latexmk and pdfLaTeX. The final
build produced an 18-page PDF with no LaTeX warnings, overfull boxes,
underfull boxes, or unresolved-reference markers in the log/text checks.
The PDF has 29 outline entries. All pages were rendered and reviewed in
contact sheets; key formula pages and the final title, contents, and
references pages were also inspected at readable resolution. Text boxes
were checked against the page margins.

The proposed manuscript insert was separately compiled successfully in a
minimal book-class harness with the expected theorem environments and
`\Li` command. That check produced three pages. It is a syntax and layout
check, not a claim that the full upstream manuscript was rebuilt.

`make test` completed with exit code zero. `verification.log` contains the
actual standard output and environment versions. The exact reports,
153-case numerical report, rational interval certificate, and independent
standard-library replay report all record PASS.

The package does not contain a Lean development, a Wolfram session, or a
claim of independent peer review. Mathematical soundness rests on the
arguments in the article; implementation checks and analytic error bounds
are distinguished there. No upstream files were edited or committed.
