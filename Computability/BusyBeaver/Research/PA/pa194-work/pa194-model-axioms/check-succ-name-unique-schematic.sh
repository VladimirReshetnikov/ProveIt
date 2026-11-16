#!/usr/bin/env bash
set -euo pipefail
repo=${1:?repository root required}
out=${2:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
sha256sum -c "$here/succ-name-unique-schematic-pins.sha256"
export LEAN_PATH="$out:/dev/shm/pa194-succ-unique-schematic-repo:/dev/shm/pa194-name-forms-repo:/dev/shm/pa194-full-one-level-audit:$(lake env printenv LEAN_PATH)"
lean -j1 -M 5000 -R "$here" -o "$out/PA194SuccNameUniqueSchematic.olean" "$here/PA194SuccNameUniqueSchematic.lean" > "$out/PA194SuccNameUniqueSchematic.log" 2>&1
if rg -q 'error:|error\(|sorryAx' "$out/PA194SuccNameUniqueSchematic.log"; then cat "$out/PA194SuccNameUniqueSchematic.log"; exit 1; fi
cat "$out/PA194SuccNameUniqueSchematic.log"
echo 'PASS: schematic successor-name uniqueness source replay'
