# Final PDF quality review

Final article: `gowers_asymptotic_constants.pdf`, 35 pages, A4.

SHA-256:
`97b553d7a9cf4e2be29702225cd68824a870d135a2127066da1c864bcd601219`.

The article was compiled with `latexmk` and pdfLaTeX. The final build completed
successfully, with no remaining LaTeX warnings, undefined or multiply defined
references, or overfull boxes. The source and PDF hashes, page count, and
environment are recorded in `data/build_validation.json` and
`data/environment.json`.

All 35 pages were rendered and visually inspected across separate review passes.
The front matter and norm proofs were checked by the coordinating instance;
the cube/localization sections and back matter were inspected by separate
instances. A final typesetting pass placed the norm figure immediately after
the norm section and the localization figure before the research agenda.
Subsection headings were also kept with their following text, and the appendix starts on a fresh page. The pages whose contents changed in the final passes were inspected again.

The final title page, contents, equations, theorem statements, tables, figures,
page headers, bibliography, and source audit are readable and do not overlap or
clip. The figures show proved formula expressions and identify approximate
decimal evaluation; they do not portray numerically estimated optima as proved.

This review concerns presentation and compilation. The separate mathematical
review notes describe the proof checks; neither kind of review is a formal
proof-assistant certificate or external peer review.
