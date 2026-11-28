#!/usr/bin/env bash
set -euo pipefail
report_dir="$(cd -- "$(dirname -- "$0")/.." && pwd)"
expected_mathlib="56a005855ea17e0b0958f73ec801ae140b0a1679"

if [[ $# -gt 1 ]]; then
  printf '%s\n' "Usage: bash scripts/verify_lean.sh [existing-mathlib-checkout]" >&2
  exit 2
fi

if [[ $# -eq 1 ]]; then
  mathlib_dir="$(cd -- "$1" && pwd)"
  actual_mathlib="$(git -C "$mathlib_dir" rev-parse HEAD)"
  if [[ "$actual_mathlib" != "$expected_mathlib" ]]; then
    printf '%s\n' "The supplied Mathlib checkout does not match the pinned revision." >&2
    exit 2
  fi
  cd -- "$mathlib_dir"
else
  cd -- "$report_dir"
  lake update
  lake exe cache get
fi

lean_version="$(lake env lean --version)"
printf '%s\n' "$lean_version"
case "$lean_version" in
  "Lean (version 4.35.0,"*) ;;
  *)
    printf '%s\n' "Expected Lean 4.35.0." >&2
    exit 2
    ;;
esac

lake env lean "$report_dir/lean/HeightPower.lean"
lake env lean "$report_dir/lean/MatrixChainBudget.lean"
printf '%s\n' "Both standalone files passed. This is not a full GRH source build."
