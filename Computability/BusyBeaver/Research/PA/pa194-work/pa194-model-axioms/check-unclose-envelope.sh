#!/usr/bin/env bash
set -euo pipefail
if (($# != 3)); then echo 'usage: REPO CLOSED_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); closed=$(realpath "$2"); out=$(realpath -m "$3")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 d3cdea20bf89577944301107abd800275b70f211211f7b201865abe11afecba2 "$src/PA194UncloseOnce.lean" \
 909e38305c0cdf7d45fe8fc16977b34d2c38057c3ddd9c12552333d42806c80c "$src/PA194UncloseTrace.lean" \
 913712aaf0cb3ffc9d8a4338e78ead4dda1ae7fa5bf8edf55621295af2d60896 "$src/PA194UncloseEnvelopeAudit.lean" \
 1915479ceecf82defc487dc001d9c3de9e1ecfb6ad17c257f5ec3db01221327b "$closed/PA194FullyClosedSeparation.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$closed:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194UncloseOnce PA194UncloseTrace PA194UncloseEnvelopeAudit; do
 echo "Checking $n"
 lean -j1 -M 4000 -R "$src" -o "$out/$n.olean" "$src/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194UncloseEnvelopeAudit.log") == 6 ]]
cat "$out/PA194UncloseEnvelopeAudit.log"
check_inputs
echo 'PASS: model-level bounded property recovery; staged dependencies prebuilt.'
