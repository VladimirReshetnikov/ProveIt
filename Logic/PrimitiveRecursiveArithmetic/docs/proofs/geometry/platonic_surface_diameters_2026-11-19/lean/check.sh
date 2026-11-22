#!/usr/bin/env bash
# Usage: with Lean 4.32.0 on PATH, ./check.sh /path/to/ProveIt
set -euo pipefail
source_dir="$(cd "$(dirname "$0")" && pwd)"
provider_dir="$(cd "$1" && pwd)"
module_dir="$(mktemp -d)"
trap 'rm -rf "$module_dir"' EXIT
provider_path="$(cd "$provider_dir" && lake env printenv LEAN_PATH)"
cd "$source_dir"
export LEAN_PATH="$module_dir:$provider_path"
lean --version
for module in SmallCertificates Icosahedron DodecaLower DodecaUpper IntrinsicIPRA TetrahedronIPRA IcosahedronIPRA DodecahedronIPRA; do
    lean -o "$module_dir/$module.olean" "$module.lean"
    echo "Checked $module.lean"
done
