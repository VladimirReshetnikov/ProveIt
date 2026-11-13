#!/usr/bin/env bash
set -euo pipefail
task_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
proveit_dir="${1:?Usage: bash scripts/check_lean.sh /absolute/path/to/ProveIt}"
cd "$proveit_dir"
command -v lake >/dev/null
lake env lean "$task_dir/lean/ProofCore.lean"
lake env lean "$task_dir/lean/MathlibAssembly.lean"
lake env lean "$task_dir/lean/Statement.lean"
