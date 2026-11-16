#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
"${LEAN_BIN:-lean}" FiniteCore.lean
"${LEAN_BIN:-lean}" Targets.lean
"${LEAN_BIN:-lean}" FiniteBranch.lean
