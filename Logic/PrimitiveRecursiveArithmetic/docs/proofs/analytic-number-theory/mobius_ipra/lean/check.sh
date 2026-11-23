#!/bin/sh
set -eu
cd "$(dirname "$0")"
compiler=${LEAN:-lean}
cache=$(mktemp -d)
trap 'rm -rf "$cache"' EXIT
"$compiler" --version
"$compiler" -o "$cache/FiniteInversion.olean" FiniteInversion.lean
LEAN_PATH="$cache${LEAN_PATH:+:$LEAN_PATH}" "$compiler" FormalSeries.lean
