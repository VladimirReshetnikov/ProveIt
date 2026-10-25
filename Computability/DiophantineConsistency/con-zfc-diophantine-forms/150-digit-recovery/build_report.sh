#!/usr/bin/env bash
set -euo pipefail
report_root="$(cd -- "$(dirname -- "$0")" && pwd)"
report_tmp="$(mktemp -d /tmp/conzfc_report.XXXXXXXX)"
trap 'rm -rf -- "$report_tmp"' EXIT
command -v pdflatex >/dev/null
build_one() {
    local source_dir="$1"
    local source_name="$2"
    local output_name="$3"
    local build_dir="$4"
    mkdir -p "$build_dir"
    for pass in 1 2 3; do
        if ! (cd "$source_dir" && pdflatex -interaction=nonstopmode -halt-on-error \
            -output-directory="$build_dir" "$source_name.tex" >"$build_dir/pass-$pass.txt"); then
            cat "$build_dir/pass-$pass.txt"
            return 1
        fi
    done
    if grep -E 'Overfull|undefined references|Citation .* undefined|Reference .* undefined' \
        "$build_dir/$source_name.log"; then
        printf '%s\n' "Report layout or cross-reference warning requires review."
        return 1
    fi
    cp "$build_dir/$source_name.pdf" "$output_name"
}
build_one "$report_root" article "$report_root/article.pdf" "$report_tmp/main"
experiment="$report_root/experiments/three_parameter_calculus"
build_one "$experiment" research_note "$experiment/research_note.pdf" "$report_tmp/experiment"
printf '%s\n' "Built article.pdf and experiments/three_parameter_calculus/research_note.pdf"
