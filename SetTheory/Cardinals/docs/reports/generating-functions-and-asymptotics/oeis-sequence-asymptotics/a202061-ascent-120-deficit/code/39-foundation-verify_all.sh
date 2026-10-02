#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
for script in critical_certificate.py block_formula.py check_operators.py check_height_walk.py check_word_states.py check_narayana.py check_staircase.py; do
  printf '\n== %s ==\n' "$script"
  python "$script"
done
printf '\nAll author-side mathematical diagnostics passed.\n'
