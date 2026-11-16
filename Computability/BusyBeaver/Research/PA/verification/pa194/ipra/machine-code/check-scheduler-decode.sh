#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO DECODER_SOURCE NEW_SOURCE FETCH_OUTPUT FETCH_LOG PROJECT_FOUNDATION PACKAGE_FOUNDATION NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); decoder=$(realpath "$2"); source=$(realpath "$3"); base=$(realpath "$4"); base_log=$(realpath "$5"); project=$(realpath "$6"); package=$(realpath "$7"); out="$8"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
check_sources() { printf '%s  %s\n' \
 e2d0f7ce5f68d2bac7b14ca00edcb4a270f545d0c1f2b1f7a0e0c3204242cd4d "$source/PA194DecoderInvariant3.lean" \
 9d5c1897201d34bc5b94c4f88e138854f9162fbc6b0630c1be9825f1006e617c "$source/PA194DecoderSynchronization.lean" \
 959ce89af978b4d630f9db9febb98f544b93989eb3ddc6e5956ed1601a8fb1d7 "$source/PA194DecoderClock.lean" \
 e53e307792d053c8019e8ccce9971c0c74399c28ab8973315d0cc8b4b225d96c "$source/PA194DecoderComplete.lean" \
 631f5b288d683f1bd68e883c9309b4e0e3f176abd588f7a392d5eb5ecf9475f6 "$source/PA194SchedulerDecode.lean" | sha256sum -c -; }
check_sources
"$source/check-decoder-round-code.sh" "$repo" "$decoder" "$source" "$base" "$base_log" "$project" "$package" "$out"
out=$(realpath "$out")
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194DecoderInvariant3 PA194DecoderSynchronization PA194DecoderClock PA194DecoderComplete PA194SchedulerDecode; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
for spec in PA194DecoderInvariant3:bodyDef PA194DecoderSynchronization:synchronization PA194DecoderClock:accumulate PA194DecoderComplete:decode PA194DecoderComplete:decodeFromZero PA194SchedulerDecode:fetchAndDecode; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_sources
echo 'PASS: model-length actual source fetch and Cantor decode against scheduler projections; graph and general foundations remain prebuilt.'
