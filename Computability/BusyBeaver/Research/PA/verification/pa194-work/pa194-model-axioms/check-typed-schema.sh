#!/usr/bin/env bash
set -euo pipefail
if (($# != 3)); then echo 'usage: REPO CLOSED_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); closed=$(realpath "$2"); out=$(realpath -m "$3")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 eb222db2ef268ed169559500f22797e8143a6a2589c83e36453ab13958b2bbd1 "$src/PA194TypedSepQuote.lean" \
 e3f4b98838553c9646f029423d6800a4e245c37ea8511a49673cc98cdc8b7d8f "$src/PA194TypedFix.lean" \
 dae3be6145015a18e306f4dcb001aa06faf065748a102d051362e0257a2842d0 "$src/PA194TypedClosure.lean" \
 9f339a59a4b7a88f5d86a9488ab8dbdb053de41d83ec90f1981915b88d3d2c7c "$src/PA194TypedBound.lean" \
 5e4e4720a4cd44394d7893e22b5f16f8db8d02f8b08496b9d5ec080657747946 "$src/PA194TypedSchema.lean" \
 77311fd55ce192d83f884716a2d92b77e133568c2e2f62c941a6fd8209e2f7a9 "$src/PA194TypedSchemaAudit.lean" \
 1915479ceecf82defc487dc001d9c3de9e1ecfb6ad17c257f5ec3db01221327b "$closed/PA194FullyClosedSeparation.olean" \
 2ee807d46c5c189ed97eef6f6f66df02d57811f4a6c743145701589a0e6d486b /dev/shm/pa194-adjunctive-admission-audit/PA194SourceSeparation.olean \
 40a30f8715da59e118d4e337dc8ab5969186805af540bcb24300dba2f51e8ba5 /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Foundation/FirstOrder/Incompleteness/InductionSchemeDelta1.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$closed:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194TypedSepQuote PA194TypedFix PA194TypedClosure PA194TypedBound PA194TypedSchema PA194TypedSchemaAudit; do
 echo "Checking $n"
 lean -j1 -M 4000 -R "$src" -o "$out/$n.olean" "$src/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194TypedSchemaAudit.log") == 10 ]]
cat "$out/PA194TypedSchemaAudit.log"
check_inputs
echo 'PASS: typed Foundation separation schema quotation in PRA plus IΣ₁ models; staged dependencies prebuilt.'
