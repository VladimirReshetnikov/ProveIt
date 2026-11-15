#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 ca219ae3a32a0eb1edad152e185c805272e9682e80b38d6b620ddcebb8f22637 "$src/PA194SeparationShiftCode.lean" \
 13377de38cd9880d7675dcc0bce97188f56a3e10538e505fa16da8126dbe7c79 /dev/shm/pa194-internal-separation-shift-repo/PA194InternalSeparationShift.olean \
 1ed2f47fd0d3adb6d77f6e5c14e704980d1233dca7742199a787c829523f7940 /dev/shm/pa194-uniform-sep-combined-repo/PA194ModelSepRootGraph.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-uniform-sep-combined-repo:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194SeparationShiftCode.olean" "$src/PA194SeparationShiftCode.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 6 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: uniform graphs and internal proof codes for shifting separation and negated separation; dependencies prebuilt.'
