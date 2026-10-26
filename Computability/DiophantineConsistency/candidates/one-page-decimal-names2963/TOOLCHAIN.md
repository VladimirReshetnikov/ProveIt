# Four held commands; ROOT executes each independently

NOT RUN. No execution authority is supplied by this file. Review exact SOURCE_PINS
and the closed manifest first; later ROOT release is separate. No eval/wrapper script.

ROOT inert preflight after release: authenticate the whole packet and all pins;
check `/usr/bin/pdflatex` is symlink `pdftex` resolving to pinned `/usr/bin/pdftex`;
require the fixed /tmp tree absent (including symlinks). Create that tree once and
copy ONLY pinned equation.tex to its equation.tex using an inert exclusive writer;
verify the whole copy equals the original. All four working directories are exactly
`/tmp/decimal-names2963-fit-v1`. Never substitute live main equation.tex.
ROOT retains command text and tool-observed actual exit in 01.exit through 04.exit
using inert exclusive writers AFTER each process; no shell wrapper hides its status.
Require each destination/log absent before its command; preserve all output bytes.

1. Compile exactly once. SOURCE_DATE_EPOCH/FORCE_SOURCE_DATE/TZ are fixed;
   env -i removes inherited TeX overrides; shell escape is off; input/output are
   paranoid. Installed trusted format/package/font reads remain necessary.

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C TZ=UTC SOURCE_DATE_EPOCH=946684800 FORCE_SOURCE_DATE=1 openin_any=p openout_any=p shell_escape=f \
  /usr/bin/pdflatex -no-shell-escape -halt-on-error -interaction=nonstopmode -file-line-error -recorder \
  -output-directory=/tmp/decimal-names2963-fit-v1 equation.tex \
  > /tmp/decimal-names2963-fit-v1/01-pdflatex.stdout 2> /tmp/decimal-names2963-fit-v1/01-pdflatex.stderr
```

2. Only after actual exit 0 and a regular, nonsymlink equation.pdf exists:

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C TZ=UTC SOURCE_DATE_EPOCH=946684800 FORCE_SOURCE_DATE=1 \
  /usr/bin/pdfinfo -isodates /tmp/decimal-names2963-fit-v1/equation.pdf \
  > /tmp/decimal-names2963-fit-v1/02-pdfinfo.stdout 2> /tmp/decimal-names2963-fit-v1/02-pdfinfo.stderr
```

3. Only after step 2 actual exit 0; keep complete layout text:

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C TZ=UTC SOURCE_DATE_EPOCH=946684800 FORCE_SOURCE_DATE=1 \
  /usr/bin/pdftotext -layout -enc UTF-8 /tmp/decimal-names2963-fit-v1/equation.pdf /tmp/decimal-names2963-fit-v1/equation.txt \
  > /tmp/decimal-names2963-fit-v1/03-pdftotext.stdout 2> /tmp/decimal-names2963-fit-v1/03-pdftotext.stderr
```

4. Only after step 3 actual exit 0. No page restriction, crop or singlefile flag:

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C TZ=UTC SOURCE_DATE_EPOCH=946684800 FORCE_SOURCE_DATE=1 \
  /usr/bin/pdftoppm -png -r 144 /tmp/decimal-names2963-fit-v1/equation.pdf /tmp/decimal-names2963-fit-v1/page \
  > /tmp/decimal-names2963-fit-v1/04-pdftoppm.stdout 2> /tmp/decimal-names2963-fit-v1/04-pdftoppm.stderr
```

Record all pages/dimensions from pdfinfo, whole logs including every overfull
warning, all text and all page-N.png files; do not filter failed/overflow evidence.
No automatic retry, repair, font change, second TeX pass or main promotion.
The exact original source and all held files remain immutable before/after.
Only fit measurement and retained-output inspection are prospective; no whole
formula/glyph validation or page acceptance is claimed by these four utilities.
