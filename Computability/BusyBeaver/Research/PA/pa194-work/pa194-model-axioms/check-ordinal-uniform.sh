#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then echo 'usage: REPO FIXED_BASE INDUCTION_BASE STATEMENT_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); fixed=$(realpath "$2"); induction=$(realpath "$3"); statement=$(realpath "$4"); out=$(realpath -m "$5")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 8912376785610c625a40ac44ea887c4b4674fca4190015aaec5a9be5ec48f500 "$src/PA194FixedSyntaxQuote.lean" \
 88a034847750031829fd302b2e96a792a2b28963980c2e57d026f15005693b53 "$src/PA194OrdinalUniform.lean" \
 54a3a34cfa4019df7711492d5617fe2c3de115d3e617b8c308af41ae23817b5f "$fixed/PA194OrdinalFixed.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$fixed:$induction:$statement:/dev/shm/pa194-typed-schema-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194FixedSyntaxQuote PA194OrdinalUniform; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194FixedSyntaxQuote.log") == 3 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194OrdinalUniform.log") == 1 ]]
check_inputs
echo 'PASS: uniform graph for ordinal induction statement; dependencies prebuilt.'
