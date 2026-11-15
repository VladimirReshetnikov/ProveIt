#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO DECODER_SOURCE NEW_SOURCE FETCH_OUTPUT FETCH_LOG PROJECT_FOUNDATION PACKAGE_FOUNDATION NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); decoder=$(realpath "$2"); source=$(realpath "$3"); base=$(realpath "$4"); base_log=$(realpath "$5"); project=$(realpath "$6"); package=$(realpath "$7"); out="$8"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
check_source() { printf '%s  %s\n' febfc0fbd1d562e619bc33bc58d71277d07c9d40dae4739eece61f17f9642e39 "$source/PA194DecoderRoundCode.lean" | sha256sum -c -; }
check_source
"$source/check-diagonal-iteration.sh" "$repo" "$decoder" "$source" "$base" "$base_log" "$project" "$package" "$out"
out=$(realpath "$out")
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$base:$base/foundation-view:$project:$package:$lake_path"
lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/PA194DecoderRoundCode.olean" "$source/PA194DecoderRoundCode.lean" > "$out/PA194DecoderRoundCode.log" 2>&1
if rg -q 'sorryAx|declaration uses .sorry.' "$out/PA194DecoderRoundCode.log"; then cat "$out/PA194DecoderRoundCode.log"; exit 1; fi
for thm in registerModel clockModel advanceModel runFive advancePositive advanceZero; do
 rg -Fq "'PA194DecoderRoundCode.$thm' depends on axioms:" "$out/PA194DecoderRoundCode.log"
done
rg 'depends on axioms:' "$out/PA194DecoderRoundCode.log"
check_source
echo 'PASS: actual PR-coded source decoder round, with exact branch-dependent clock; graph and general foundations remain prebuilt.'
