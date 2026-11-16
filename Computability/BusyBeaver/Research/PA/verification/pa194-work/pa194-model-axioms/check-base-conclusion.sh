#!/usr/bin/env bash
set -euo pipefail
if (($# != 3)); then echo 'usage: REPO TYPED_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); typed=$(realpath "$2"); out=$(realpath -m "$3")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 2feb341f8346a11c07675f72f3027b18b230e7b9f79b51087a5f5d437f463cc2 "$src/PA194InternalOrdinalConclusion.lean" \
 b6e4de73c794f2748bc459505da0ab23fec5d6bdb0c2da2278a97c76454af7e6 "$src/PA194OrdinalConclusionQuote.lean" \
 c3e8866619cd09b4dab440cd9e32a46bd27cbd2978ed04140d9c92364a989f6b "$src/PA194InternalOrdinalBase.lean" \
 8c181d8473a9f3a5d5b4fb9dd1693117cc512954dc2f8a653eb70dd22ae4b364 "$src/PA194OrdinalBaseQuote.lean" \
 90c7459104f0b1a2103d471d080efe8a0e44a2e64051f84ff6ca9c4da622f6cd "$src/PA194OrdinalBaseConclusionAudit.lean" \
 8e59d32fa05cee0e6b74201250a30040a509800897b9f7952ba0305b965cd147 "$typed/PA194TypedSepQuote.olean" \
 7dc0b4c79caf4e100e1d59dcf9df3c18d9d75e8e320dd227257f538d3f8b5107 /dev/shm/pa194-adjunctive-admission-audit/PA194FoundationOrdinalInductionSchema.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$typed:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194InternalOrdinalConclusion PA194OrdinalConclusionQuote PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194OrdinalBaseConclusionAudit; do
 echo "Checking $n"
 lean -j1 -M 4000 -R "$src" -o "$out/$n.olean" "$src/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194OrdinalBaseConclusionAudit.log") == 6 ]]
cat "$out/PA194OrdinalBaseConclusionAudit.log"
check_inputs
echo 'PASS: definable ordinal-induction base and conclusion constructors and typed quote; dependencies prebuilt.'
