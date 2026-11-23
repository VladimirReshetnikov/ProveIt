#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work"
lean --version
lean -o "$work/GraphCore.olean" GraphCore.lean
lean -o "$work/CutParity.olean" CutParity.lean
lean -o "$work/ColorCert.olean" ColorCert.lean
lean Check.lean
