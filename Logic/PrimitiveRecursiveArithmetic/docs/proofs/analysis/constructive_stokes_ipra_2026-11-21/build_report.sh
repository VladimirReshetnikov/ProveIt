#!/usr/bin/env bash
# Build the report with local TeX Live files.  No network access is used.
# Usage: ./build_report.sh [path/to/report.tex]
# STOKES_TEX_CACHE can select a writable scratch directory for format/log files.
set -euo pipefail

package_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
source_file="${1:-$package_dir/report/report.tex}"
source_dir="$(cd -- "$(dirname -- "$source_file")" && pwd)"
source_name="$(basename -- "$source_file")"
job_name="${source_name%.tex}"
cache_dir="${STOKES_TEX_CACHE:-${TMPDIR:-/tmp}/stokes-tex-${UID:-user}}"
mkdir -p "$cache_dir/formats" "$cache_dir/maps" "$cache_dir/logs"
cache_dir="$(cd -- "$cache_dir" && pwd)"

command -v pdflatex >/dev/null
command -v kpsewhich >/dev/null
tex_args=()

if [[ -z "$(kpsewhich amsmath.sty 2>/dev/null)" ||
      -z "$(kpsewhich -format=fmt pdflatex.fmt 2>/dev/null)" ||
      -z "$(kpsewhich pdftex.map 2>/dev/null)" ]]; then
  # Some minimal Debian images contain all package files but omit generated
  # ls-R databases, formats and font maps.  Search the real trees directly,
  # and reconstruct only the needed generated files in our scratch directory.
  test -d /usr/share/texlive/texmf-dist
  test -d /usr/share/texmf
  export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf,/etc/texmf}'
  export TEXFONTMAPS="$cache_dir/maps//:"
  if [[ ! -s "$cache_dir/formats/pdflatex.fmt" ]]; then
    if ! (cd "$cache_dir/formats" && pdftex -ini -etex -jobname=pdflatex \
        -progname=pdflatex -interaction=nonstopmode -halt-on-error \
        pdflatex.ini) >"$cache_dir/logs/format.log" 2>&1; then
      tail -80 "$cache_dir/logs/format.log" >&2
      exit 1
    fi
  fi
  cat \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cmextra.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/latxfont.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map \
    /usr/share/texmf/fonts/map/dvips/lm/lm.map \
    >"$cache_dir/maps/pdftex.map"
  tex_args+=("-fmt=$cache_dir/formats/pdflatex.fmt")
fi

for pass in 1 2 3; do
  if ! (cd "$source_dir" && pdflatex "${tex_args[@]}" \
      -interaction=nonstopmode -halt-on-error -file-line-error "$source_name") \
      >"$cache_dir/logs/$job_name-pass$pass.log" 2>&1; then
    tail -100 "$cache_dir/logs/$job_name-pass$pass.log" >&2
    exit 1
  fi
done

printf 'Built %s/%s.pdf\n' "$source_dir" "$job_name"
printf 'Build logs: %s/logs\n' "$cache_dir"
