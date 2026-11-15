#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO DECODER_SOURCE NEW_SOURCE FETCH_OUTPUT FETCH_LOG PROJECT_FOUNDATION PACKAGE_FOUNDATION NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); decoder=$(realpath "$2"); source=$(realpath "$3"); base=$(realpath "$4"); base_log=$(realpath "$5"); project=$(realpath "$6"); package=$(realpath "$7"); out="$8"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
check_sources() {
 printf '%s  %s\n' \
 f0147c08af606feaea7c3da8b5142039dbae85dd44cc88a4ea47b80acb13dfbd "$source/PA194UnpairExit.lean" \
 fe146ccc98edf4c035a6c500ab4543de4e4667c576cb0317d4dd26cce325e103 "$source/PA194UnpairCantor.lean" | sha256sum -c -
}
check_sources
"$decoder/check-unpair-after-fetch.sh" "$repo" "$decoder" "$base" "$base_log" "$project" "$package" "$out"
out=$(realpath "$out")
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194UnpairExit PA194UnpairCantor; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
for spec in PA194UnpairExit:exitTo42 PA194UnpairCantor:positiveCantor PA194UnpairCantor:zeroCantor PA194UnpairCantor:positiveRoundInvariant PA194UnpairCantor:zeroRoundInvariant PA194UnpairCantor:exitIdentifies; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_sources
echo 'PASS: decoder rounds, exact Cantor invariant and site-42 scheduler projection identification; graph and general foundations remain prebuilt.'
