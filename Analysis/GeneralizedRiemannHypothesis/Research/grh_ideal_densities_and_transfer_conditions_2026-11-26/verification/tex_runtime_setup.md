# Local PDF build environment

The installed pdfTeX executable and TeX source/font trees were complete, but the normal system-generated format, language configuration, font map, and filename database were absent. No system file or report source was changed. The build used scratch-only configuration under `.tex-runtime`.

The environment (absolute scratch paths in this workspace) is:

```sh
export TEXMF='{/workspace/scratch/c88b3ed6c798/.tex-runtime/texmf,/usr/share/texmf,/usr/share/texlive/texmf-dist}'
export TEXMFVAR=/workspace/scratch/c88b3ed6c798/.tex-runtime/var
export TEXMFCONFIG=/workspace/scratch/c88b3ed6c798/.tex-runtime/config
export TEXFORMATS=/workspace/scratch/c88b3ed6c798/.tex-runtime/formats
export VARTEXFONTS=/workspace/scratch/c88b3ed6c798/.tex-runtime/fonts
```

`TEXMF` deliberately omits database-only `!!` prefixes, permitting ordinary filesystem lookup. A local `texmf/tex/generic/config/language.dat` contains:

```text
english hyphen.tex
=usenglish
=USenglish
=american
```

The local `texmf/fonts/map/pdftex/pdftex.map` combines distinct first-field font names from these installed source maps, retaining the first occurrence (752 entries):

- `/usr/share/texmf/fonts/map/dvips/lm/lm.map`
- `/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map`
- `/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cmextra.map`
- `/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map`
- `/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/latxfont.map`
- `/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/euler.map`

The format was generated from `.tex-runtime/formats` after sourcing the environment:

```sh
pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
  -jobname=pdflatex -progname=pdflatex pdflatex.ini
```

The report was compiled three times from `artifacts`:

```sh
source ../.tex-runtime/env.sh
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error report.tex
```

The first successful build produced 23 pages; two subsequent passes settled the table of contents and references at 24 pages. The third-pass log has no undefined-reference, undefined-citation, or rerun warning. Layout warnings remain for the parent editor to review. Logs are `pdflatex_format_build.log`, `latex_first_success_attempt.log`, `latex_second_pass.log`, and `latex_third_pass.log`. Any later editorial build supersedes these early PDF properties.

This initialization is peculiar to the current incomplete system installation. On an ordinary TeX Live installation, the report needs only a normal pdfLaTeX build with the packages declared in `report.tex`.
