#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 a7e57456db7d69e40a66acca3d01ab3931c2f64329f087ad6a998f5e4f9ccefb "$src/PA194FullSepOpen.lean" \
 74215847c2d64ed0e036e3597b478ad4f96d3778d8d43fd590d8ad38c90824ff /dev/shm/pa194-reopen-proof-repo/PA194ReopenProof.olean \
 3ef07833607e8a60981f53d9f0fba7f55b16b578f71a9c5026ad9bd7ecf85dfe /dev/shm/pa194-full-sep-theory-replay/PA194AdjunctiveFullSep.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
baselines="/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-uniform-fully-closed-replay:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-closed-sep-theory-replay:/dev/shm/pa194-uniform-sep-combined-replay:/dev/shm/pa194-standard-no-free-replay:/dev/shm/pa194-closed-sep-classifier-replay:/dev/shm/pa194-fairness-full-source-replay:/dev/shm/pa194-generic-sim-replay:/dev/shm/pa194-adjunctive-sim-v2-replay:/dev/shm/pa194-shift-interface-replay:/dev/shm/pa194-unrestricted-existential-v2-replay:/dev/shm/pa194-qf-ranked-existential-audit:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-general-shift-replay:/dev/shm/pa194-general-reverse-shift-replay:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-general-freshness-audit:/dev/shm/pa194-observational-general-audit:/dev/shm/pa194-full-one-level-audit"
export LEAN_PATH="$out:/dev/shm/pa194-reopen-proof-repo:/dev/shm/pa194-full-sep-theory-replay:$baselines:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194FullSepOpen.olean" "$src/PA194FullSepOpen.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 2 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: full-separation theory supplies open source instances; dependencies prebuilt.'
