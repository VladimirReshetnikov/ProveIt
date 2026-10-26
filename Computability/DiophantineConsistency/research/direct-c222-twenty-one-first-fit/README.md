# First exact C222 layout test: preserved overflow

The frozen160-line TeX was compiled once under the distinct ROOT release
`reviews/direct-c222-twenty-one-render-plan-root-runtime-release-r1.json`,
after both full presentation and runtime static reviews. All four actual
command exits were0. The19 exact original files are preserved in outputs/,
including all stdout/stderr, exact commands/exits, recorder, log, source,
PDF, complete layout text and the single whole-page PNG. No retry occurred.

`pdfinfo` reports one612x792-point Letter page and183348 PDF bytes.
The log reports two overfull displays:158.51413pt at source line44 and
5.81573pt at line113. ROOT opened the complete1224x1584 PNG. The first
front-definition display visibly extends into the right column and
overlaps the local power definitions. This page is not accepted as a
readable complete display. The source's historical unrendered labels
remain unchanged in this first attempt; they describe its preparation.

A separate new layout may change line breaks/alignment and draft-status
prose while retaining the entire polynomial, coordinates and fonts. It
requires its own exact static review and separate ROOT runtime release.
No mathematical formula change, page promotion or Lean work follows from
this measurement. The maintained one-clause2999 page remains current.

Before this run, an ENOSPC metadata write left an empty release attempt.
It is preserved with its event under reviews/history/direct21-enospc/.
Only an unused unfinished Git auto-GC temporary pack was removed. The
held source and both first full static pairs stayed unchanged; no TeX
application was attempted until the later valid release was committed.
