#!/usr/bin/env bash
set -euo pipefail
if (($# != 12)); then echo 'usage: REPO BASELINE CARRY_STAGE DYNAMIC_CODE_STAGE ROUND_STAGE SEED_STAGE FINISH_STAGE DYNAMIC28_STAGE PROJECT PACKAGE CLOCK_SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); codes=$(realpath "$4"); round=$(realpath "$5"); seed=$(realpath "$6"); finish=$(realpath "$7"); complete=$(realpath "$8"); project=$(realpath "$9"); package=$(realpath "${10}"); source=$(realpath "${11}"); out="${12}"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
check_source() { printf '%s  %s\n' 17c94f844eb8ed9a7f38bc0795f4908b4d41664d9527bbccd29f7582578c8839 "$source/PA194Site28ClockCode.lean" | sha256sum -c -; }
check_source
"$source/check-site28-dynamic-clock.sh" "$repo" "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$complete" "$project" "$package" "$source" "$out"
out=$(realpath "$out")
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$complete:$finish:$seed:$round:$codes:$stage:$baseline:$project:$package:$lake_path"
lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/PA194Site28ClockCode.olean" "$source/PA194Site28ClockCode.lean" > "$out/PA194Site28ClockCode.log" 2>&1
rg -Fq "'PA194Site28ClockCode.modelClock' depends on axioms:" "$out/PA194Site28ClockCode.log"
if rg -q 'sorryAx|declaration uses .sorry.' "$out/PA194Site28ClockCode.log"; then cat "$out/PA194Site28ClockCode.log"; exit 1; fi
rg 'depends on axioms:' "$out/PA194Site28ClockCode.log"
check_source
echo 'PASS: PR-coded exact dynamic site-28 clock; staged machine and general foundations remain prebuilt.'
