#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$PWD"
for source in M6/Zip M6/Runtime M6/Reference230 M6/NativeMinimal; do
  lean -o "$source.olean" "$source.lean"
done
