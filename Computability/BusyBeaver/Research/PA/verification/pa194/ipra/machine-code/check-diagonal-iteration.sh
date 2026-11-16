#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO DECODER_SOURCE NEW_SOURCE FETCH_OUTPUT FETCH_LOG PROJECT_FOUNDATION PACKAGE_FOUNDATION NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); decoder=$(realpath "$2"); source=$(realpath "$3"); base=$(realpath "$4"); base_log=$(realpath "$5"); project=$(realpath "$6"); package=$(realpath "$7"); out="$8"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
check_sources() {
 printf '%s  %s\n' \
 6bfab70431565424825c25316768de4f8fe837861b3aebce4d765e9579fd1453 "$source/PA194DiagonalCode.lean" \
 d6a3d6b1af02a43ec545b06023b343861cf973de3dca8cf402270edcff852b0b "$source/PA194DiagonalIteration.lean" \
 3956a544ee48ebf28e326bd7fa92570db4887a1a922ae44cb9a7b336a4812c73 "$source/PA194DiagonalLink.lean" | sha256sum -c -
}
check_sources
"$source/check-unpair-cantor.sh" "$repo" "$decoder" "$source" "$base" "$base_log" "$project" "$package" "$out"
out=$(realpath "$out")
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194DiagonalCode PA194DiagonalIteration PA194DiagonalLink; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
for spec in PA194DiagonalCode:nextZero PA194DiagonalCode:nextPositive PA194DiagonalCode:nextEq PA194DiagonalCode:scoreNext PA194DiagonalIteration:scoreIteration PA194DiagonalLink:iterationProjects PA194DiagonalLink:positiveRoundMatches PA194DiagonalLink:zeroRoundMatches; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_sources
echo 'PASS: model-length coded diagonal invariant and scheduler projections, with one-round source correspondences; graph and general foundations remain prebuilt.'
