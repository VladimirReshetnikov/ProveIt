#!/usr/bin/env bash
# Usage: ./check-lean.sh /path/to/ProveIt (at the revision cited in README).
set -euo pipefail
src="$(cd "$(dirname "$0")/lean" && pwd)"
checkout="$(cd "${1:?Supply a ProveIt checkout path}" && pwd)"
temp="$(mktemp -d)"
trap 'rm -rf "$temp"' EXIT
cd "$checkout"
lake build IPRADerivations.Core.Tactic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Algebra.Order.Field.Basic
lake env bash -euc '
  envpaths="$(python3 -c "import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ.get(\"LEAN_PATH\",\"\").split(os.pathsep) if p))")"
  export LEAN_PATH="$2:$envpaths"
  cd "$1"
  lean --version
  for mod in Translation Axioms Bridge FrameRelations CanonicalFrame MetricIdentities ObjectLanguage; do
    lean -o "$2/$mod.olean" "$mod.lean"
    echo "$mod checked"
  done
' _ "$src" "$temp"
