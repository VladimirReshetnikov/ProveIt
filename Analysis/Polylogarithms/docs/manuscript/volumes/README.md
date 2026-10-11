# Four volumes of the collective manuscript

All volumes are authored by **ProveIt Contributors**. They share mathematical
chapter sources, notation, bibliography and evidence, with introductions that
explain their distinct themes.

| Volume | PDF | Editable driver |
|---|---|---|
| I: Polylogarithm Identities and Arithmetic Reductions | [PDF](volume-1-polylogarithm-identities.pdf) | [TeX](volume-1-polylogarithm-identities.tex) |
| II: Signed Kernels, Zero Geometry and Experimental Discovery | [PDF](volume-2-signed-kernels.pdf) | [TeX](volume-2-signed-kernels.tex) |
| III: Hurwitz Jets, Stieltjes Calculus and Gamma Correlations | [PDF](volume-3-hurwitz-stieltjes.pdf) | [TeX](volume-3-hurwitz-stieltjes.tex) |
| IV: Gamma Grids, CM Periods and Herglotz Arithmetic | [PDF](volume-4-cm-and-herglotz.pdf) | [TeX](volume-4-cm-and-herglotz.tex) |

The assignment includes every original chapter exactly once, plus the
literature appendix in Volume II. Chapter, equation and theorem numbers are
retained from the combined manuscript to keep report citations stable.
Cross-volume links use named destinations in the companion PDF files.
Keep the four PDFs in the same folder when downloading or sharing them.

From `Analysis/Polylogarithms/docs/manuscript`, rebuild the complete set with:

```powershell
py verification/build_volumes.py
```

The builder compiles each volume separately, repeats complete rounds until
the shared reference state converges, and writes the four PDFs here. It also
refreshes the committed companion-label indices in `references/`, so each
individual driver can compile without the other volumes' auxiliary files.
For an individual volume, from the manuscript directory, run LuaLaTeX three
times, for example:

```powershell
lualatex -interaction=nonstopmode -halt-on-error volumes/volume-3-hurwitz-stieltjes.tex
lualatex -interaction=nonstopmode -halt-on-error volumes/volume-3-hurwitz-stieltjes.tex
lualatex -interaction=nonstopmode -halt-on-error volumes/volume-3-hurwitz-stieltjes.tex
```

Those commands write the selected PDF in the working directory. The full
builder writes all final PDFs beside their sources in this directory.
After a source change that moves reference destinations, rebuild the full set
to refresh the companion indices and shared page references.

`verification/inspect_volumes.py` checks every PDF page, chapter coverage and
all external destinations, and renders contact sheets for visual review.
`verification/check_standalone_volumes.py` compiles each driver in its own
empty output folder, comparing its page text and links with the full build.
These document checks are separate from the mathematical proof and exact
certificate replays recorded in the editorial ledger.
