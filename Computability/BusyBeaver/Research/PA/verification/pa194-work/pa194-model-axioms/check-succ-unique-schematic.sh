#!/usr/bin/env bash
set -euo pipefail
repo=${1:?repository root required}
out=${2:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
sha256sum -c "$here/succ-unique-schematic-pins.sha256"
export LEAN_PATH="$out:/dev/shm/pa194-name-forms-repo:/dev/shm/pa194-full-one-level-audit:$(lake env printenv LEAN_PATH)"
lean -j1 -M 5000 -R "$here" -o "$out/PA194SuccUniqueSchematic.olean" "$here/PA194SuccUniqueSchematic.lean" > "$out/PA194SuccUniqueSchematic.log" 2>&1
if rg -q 'error:|error\(|sorryAx' "$out/PA194SuccUniqueSchematic.log"; then cat "$out/PA194SuccUniqueSchematic.log"; exit 1; fi
cat "$out/PA194SuccUniqueSchematic.log"
echo 'PASS: schematic successor uniqueness source replay'
