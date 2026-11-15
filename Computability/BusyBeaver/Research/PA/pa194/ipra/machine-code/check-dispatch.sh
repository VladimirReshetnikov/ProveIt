#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO DECODER_SOURCE NEW_SOURCE FETCH_OUTPUT FETCH_LOG PROJECT_FOUNDATION PACKAGE_FOUNDATION NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); decoder=$(realpath "$2"); source=$(realpath "$3"); base=$(realpath "$4"); base_log=$(realpath "$5"); project=$(realpath "$6"); package=$(realpath "$7"); out="$8"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
check_sources() { printf '%s  %s\n' \
 b29179cdfa38c0d620fd4cde171825df7a1cd1d4c887e333d64a039d457a1558 "$source/PA194Transfer42Loop.lean" \
 b3225f9486fdaaee15e1f126cd3e21af53ea614d17a0eaea476b3b9431765bdc "$source/PA194Transfer42Invariant.lean" \
 00e0e30b171e10d0d1ddcdb817a274db3017514492443e5ab6fd97a855ed4f5b "$source/PA194Transfer42Model.lean" \
 1a19caab4ee404218b910213a7a155be85c6ff5ac8bc17742962dfe175c319f5 "$source/PA194Transfer42Complete.lean" \
 d1d1e3998c128574b705227725162c3a3a221bb788503de16c73ea54060206bb "$source/PA194Transfer45Loop.lean" \
 3b4751611a918b6b8f3b356d47c0c62a8da3fb6e97d772885545048ca06871a4 "$source/PA194Transfer45Invariant.lean" \
 81168df5c6c56631154aea4f1dc6290007dd561fa4a7a77a4824ec15af50e04a "$source/PA194Transfer45Model.lean" \
 2aa3c5e13d583dd6bb4386fc788e6ce844d45316a0d2cb1b300ba5575a01adbf "$source/PA194Transfer45Complete.lean" \
 98fbe182126e483f7fdca25ab68e312dcaab5e603608fdb97d6e3b1c9e1f78b8 "$source/PA194DispatchTransfers.lean" \
 9ae72bed58f0dce93583f06acab3ebdc8c08054aef56bae34671db30a1c49001 "$source/PA194DispatchTag.lean" | sha256sum -c -; }
check_sources
"$source/check-scheduler-decode.sh" "$repo" "$decoder" "$source" "$base" "$base_log" "$project" "$package" "$out"
out=$(realpath "$out")
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194Transfer42Loop PA194Transfer42Invariant PA194Transfer42Model PA194Transfer42Complete PA194Transfer45Loop PA194Transfer45Invariant PA194Transfer45Model PA194Transfer45Complete PA194DispatchTransfers PA194DispatchTag; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
for spec in PA194Transfer42Complete:transferComplete PA194Transfer45Complete:transferComplete PA194DispatchTransfers:transferToDispatch PA194DispatchTag:shiftTag PA194DispatchTag:mpTag PA194DispatchTag:axTag; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_sources
echo 'PASS: model-length source dispatch transfers and pinned tag branches; graph and general foundations remain prebuilt.'
