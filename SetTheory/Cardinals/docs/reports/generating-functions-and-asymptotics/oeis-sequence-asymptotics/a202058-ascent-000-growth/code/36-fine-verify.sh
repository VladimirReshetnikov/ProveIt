#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export MPLCONFIGDIR="$PWD/.build/matplotlib"
mkdir -p "$MPLCONFIGDIR"
./build.sh
python3 verify.py "$@"
