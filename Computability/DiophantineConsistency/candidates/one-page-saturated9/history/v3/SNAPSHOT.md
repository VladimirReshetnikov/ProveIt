# Historical v3 D2-wrap checkpoint and vertical fit-guard failure

This inert snapshot preserves all ten active candidate files, the exact
external renderer and complete third failure transcript. Existing history/v1
and history/v2 and all source dependencies remain preserved separately;
those trees are not recursively duplicated. Archived paths/pins are
provenance, not a standalone executable checkout.

The reviewed v3 TeX was46751cd577ecaebcc20b2895eb935019ac3ab447a1b5364d0b2086526281b4d7;
TOOL_PINS was5ac813abd3a8a1583423951784c9fa79d1b8d1862f6ffbd255b8c6f224ca4b58.
Both delta reviews approved it and root released five commands. The first
scratch renderer removed every horizontal overflow and produced onepage
of163670bytes, but its strict guard rejected one0.46492-point vertical
overflow. No PDF/data/success receipt was materialized and no actual auditor
or pure rebuild ran. FAILURE.stderr.txt preserves the full failure.
Root selected only paragraphgap1pt to.8pt for the next unexecuted revision;
fonts, every formula/seed and both executable tools remain unchanged.
