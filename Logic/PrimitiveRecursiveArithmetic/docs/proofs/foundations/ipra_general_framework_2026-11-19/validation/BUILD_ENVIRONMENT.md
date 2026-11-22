# PDF build environment

The installed pdfTeX was TeX Live 2025/dev/Debian, with LaTeX 2024-11-01.
Its shared TeX files were present, but the format database and default
font map had not been generated. A local `pdflatex.fmt` was created with
`pdftex -ini -etex -jobname=pdflatex '\input pdflatex.ini'`, using

```
TEXMF={/usr/share/texlive/texmf-dist,/usr/share/texmf}
```

The local `pdftex.map` combined the installed Latin Modern map
`/usr/share/texmf/fonts/map/dvips/lm/lm.map` and the installed AMS font maps
under `/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/`.

The successful command used `pdflatex -fmt=<local pdflatex.fmt>
-interaction=nonstopmode -halt-on-error report.tex`, with `TEXFONTMAPS`
pointing to the local map directory. Repeated passes resolved references
and the table of contents. These local runtime files are not part of the
mathematical source and need not be copied into a configured TeX installation.

The final PDF was rendered to page images for visual inspection. The report
records no Lean build: the executable was unavailable.
