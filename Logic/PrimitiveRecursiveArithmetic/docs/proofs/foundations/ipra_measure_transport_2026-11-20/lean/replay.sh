#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
LEAN_LAKE_BIN="${LEAN_LAKE_BIN:-lake}"
"$LEAN_LAKE_BIN" build
