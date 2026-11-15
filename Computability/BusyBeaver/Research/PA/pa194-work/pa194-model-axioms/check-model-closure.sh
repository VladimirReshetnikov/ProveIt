#!/usr/bin/env bash
set -euo pipefail
if (($# != 6)); then echo 'usage: REPO GENERAL_BASE OPEN_SEPARATION_BASE OPEN_FORMULA_BASE FULL_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); gen=$(realpath "$2"); sep=$(realpath "$3"); op=$(realpath "$4"); base=$(realpath "$5"); out=$(realpath -m "$6")
source_dir=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 03785902de5b83e012b60d8749b5a4fb517c43e24aa61ed05a44b916186c3a37 "$source_dir/PA194CloseOne.lean" \
 ffb68ffe21b450bbc981c3088e6398c101029c7848b2bdf155ddafc0c5c7febe "$source_dir/PA194CloseHistory.lean" \
 f1041ef71595ca20ac8560ac40ef189c8cf2d1d91871febebe74f1b37167856c "$source_dir/PA194CloseTraceLift.lean" \
 29301116261fba0af9b24dbb04ac628119f17abb3bdfe2008bb07d758736d53b "$source_dir/PA194PushHistory.lean" \
 5fb1e0c957c9d42a927512726781296b1df67ddc8128d3c776ce0781ff4d6011 "$source_dir/PA194ModelClosureAudit.lean" \
 2064123c1d2b1651d207ceaf4ba79a42d88f191e9a735453f36dfad6775aa59e "$gen/PA194BoundSeparation.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$gen:$sep:$op:/dev/shm/pa194-adjunctive-admission-audit:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194CloseOne PA194CloseHistory PA194CloseTraceLift PA194PushHistory PA194ModelClosureAudit; do
 echo "Checking $n"
 lean -j1 -M 4000 -R "$source_dir" -o "$out/$n.olean" "$source_dir/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194ModelClosureAudit.log") == 15 ]]
cat "$out/PA194ModelClosureAudit.log"
check_inputs
echo 'PASS: definable model-length repeated binding and target lifting in PRA plus IΣ₁ models; staged baselines and foundations prebuilt.'
