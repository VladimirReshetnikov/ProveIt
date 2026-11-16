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
 50c6e984030a801bd2ae4f81fb14160d4b50e241ba6ecf2733e458ef627363c2 "$src/PA194InternalOrdinalStep.lean" \
 2f45fb05aea8e2bbf7b5e3f9469f17c127073a85dbf745c8db8c395d8491f87e "$src/PA194OrdinalStepQuote.lean" \
 f1c4b766975bc4630e9a2b63d047868409e59796ab6a0bcf74331efd8ba6a11d "$src/PA194InternalOrdinalStatement.lean" \
 f29a77079ac4b28dfece6dc81978e9f57efc1bd87e426727251b48e2c50426eb "$src/PA194OrdinalStatementQuote.lean" \
 4aa6890cd498d36a33253d92eb33131bdb6ab9b21e8d0d728c7ee0c9a2e2b50b "$src/PA194OrdinalStatementAudit.lean" \
 faae8469e628599a0744e01a790b819ac0c6b234fb5cc6a4207f9cb0c9a5435e /dev/shm/pa194-adjunctive-admission-audit/PA194FoundationOrdinalInductionNumeric.olean \
 8e59d32fa05cee0e6b74201250a30040a509800897b9f7952ba0305b965cd147 "$typed/PA194TypedSepQuote.olean" \
 7dc0b4c79caf4e100e1d59dcf9df3c18d9d75e8e320dd227257f538d3f8b5107 /dev/shm/pa194-adjunctive-admission-audit/PA194FoundationOrdinalInductionSchema.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$typed:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194InternalOrdinalConclusion PA194OrdinalConclusionQuote PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194InternalOrdinalStep PA194OrdinalStepQuote PA194InternalOrdinalStatement PA194OrdinalStatementQuote PA194OrdinalStatementAudit; do
 echo "Checking $n"
 lean -j1 -M 4000 -R "$src" -o "$out/$n.olean" "$src/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194OrdinalStatementAudit.log") == 12 ]]
cat "$out/PA194OrdinalStatementAudit.log"
check_inputs
echo 'PASS: definable ordinal-induction statement component constructors and typed quote; dependencies prebuilt.'
