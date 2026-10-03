# Producer PDF visual verification

Date: 2 October 2026.

The complete 17-page PDF was rebuilt with two pdfLaTeX passes, rasterized with Poppler at 90 dpi, and every page image was inspected. Mathematical displays, numbering, headings, margins, page transitions and references are legible; no clipping, overlap, missing glyphs or unresolved references was found. The build log has no overfull boxes. These visual checks supplement the separate mathematical and integrated-source audits.

Reviewed PDF SHA256: `0e850d5b85b070f95b8980a8351f282b6d9a8814ae0462f113244c7b42439e98`.

The PDF timestamp is fixed by the build script. Page rasterizations and TeX build caches are local QA intermediates, excluded from the release payload.

The final subkernel-weight clarification was rebuilt; pages 14–17 were rerendered and rechecked. Earlier pages were unchanged. No new layout defect appeared.
