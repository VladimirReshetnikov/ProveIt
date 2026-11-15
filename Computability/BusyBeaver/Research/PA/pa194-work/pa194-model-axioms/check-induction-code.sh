#!/usr/bin/env bash
set -euo pipefail
if (($# != 4)); then echo 'usage: REPO STATEMENT_BASE TYPED_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); statement=$(realpath "$2"); typed=$(realpath "$3"); out=$(realpath -m "$4")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 3a15c7b02b629b838d0978ecdab8eaeca610622c7d27a6be5d55abe60313c4c8 "$src/PA194OrdinalPropertyPlacement.lean" \
 0ecfa212c5d9fd2934467962689de76838e9fcd397a157bbf1a9087af3829f77 "$src/PA194OrdinalStepFromProperty.lean" \
 54bab440a35b1c3167dfd8f77741950cba516561bdb420fba894e773305e6d1b "$src/PA194OrdinalStatementFromProperty.lean" \
 1b56e58dd7befb1639f007f7f56d238fca839415b450161c5ecd726ff05a69b8 "$src/PA194OrdinalInductionCodeAudit.lean" \
 98dc894d318989f0f7f08d5f282ddcdda939d52b7cb83e577cdd586656c19a10 "$statement/PA194OrdinalStatementQuote.olean" \
 6b09d61d1b325cd7fa9d872f3c32d7762162620f6ee79eb13f52400246cb6007 "$statement/PA194OrdinalStepQuote.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$statement:$typed:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194OrdinalPropertyPlacement PA194OrdinalStepFromProperty PA194OrdinalStatementFromProperty PA194OrdinalInductionCodeAudit; do
 echo "Checking $n"
 lean -j1 -M 4000 -R "$src" -o "$out/$n.olean" "$src/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194OrdinalInductionCodeAudit.log") == 8 ]]
cat "$out/PA194OrdinalInductionCodeAudit.log"
check_inputs
echo 'PASS: internal ordinal induction syntax from one property, with explicit template inputs; dependencies prebuilt.'
