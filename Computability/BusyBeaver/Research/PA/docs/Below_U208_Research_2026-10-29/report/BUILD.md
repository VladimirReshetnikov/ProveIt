# Build the research report

Run `bash build_pdf.sh` in this directory with pdfLaTeX and the packages
geometry, fontenc, Latin Modern, microtype, amsmath, amssymb, amsthm,
mathtools, booktabs, longtable, array, enumitem, xurl, seqsplit and hyperref.
The script performs two passes. No network is required.

The main editable source is report.tex; status.tex and boundary_status.tex
contain the final outcome and projection-specific text.

For environments lacking a writable TeX format cache, generate a local format
in a writable temporary directory using:

    pdflatex -ini -jobname=pdflatex -progname=pdflatex '*pdflatex.ini'

Then set PDFLATEX_FORMAT to its absolute .fmt path before running the script.
PDF bytes can vary with engine version and timestamps; mathematical input
identities and tables are checked independently in the audit packet.

Render for visual review with:

    pdftoppm -r 110 -png report.pdf render/page

All rendered pages must be reviewed after substantive final edits.
