#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lean_bin="${1:-lean}"
{
  "$lean_bin" --version
  "$lean_bin" -o AffineBounds.olean AffineBounds.lean
  "$lean_bin" -o SmallGainBlueprint.olean SmallGainBlueprint.lean
  LEAN_PATH=".:${LEAN_PATH:-}" "$lean_bin" -o TowerBlueprint.olean TowerBlueprint.lean
  LEAN_PATH=".:${LEAN_PATH:-}" "$lean_bin" -o MatrixBlueprint.olean MatrixBlueprint.lean
} > validation.log 2>&1
cat validation.log
case "$(<validation.log)" in
  *sorryAx*|*error:*) exit 1 ;;
esac
printf '%s\n' 'Compiled 18 arithmetic proofs and three definition/target blueprints.'
printf '%s\n' 'Blueprint target propositions remain unproved; ObjectAdapter is not compiled.'
