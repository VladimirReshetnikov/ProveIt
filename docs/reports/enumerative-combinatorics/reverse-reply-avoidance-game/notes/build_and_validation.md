# Build and validation record

The final article was compiled successfully with pdfLaTeX through latexmk.
The output is an A4 PDF with 14 pages, an embedded bibliography, clickable
cross-references, and PDF section bookmarks. No undefined references or
citations and no overfull boxes were reported. One mild underfull box in the
proof-audit table is harmless.

The PDF was rendered to images and visually inspected, including the cover,
all body pages in contact sheets, the main stability/minimality page, and the
worked-certificate and audit sections. The table of contents was compacted to
fit on the first page. Automated text-block checks found no text outside the
page margins and no Unicode replacement characters.

The packaged Python verification was rerun successfully. The packaged optional
exploration was also rerun at k=5 and k=6 and reproduced the original discovery
counts. No test result is a proof-assistant certificate or external review.

Compilation intermediates and Python bytecode caches are not distributed.
No third-party paper or standalone font file is included.
