#!/usr/bin/env bash
set -euo pipefail
if (($# != 10)); then echo 'usage: REPO FULL_SEP SEEDED DEF CLOSURE GENERAL SEP OPEN FULL NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); fullsep=$(realpath "$2"); seeded=$(realpath "$3"); df=$(realpath "$4"); closure=$(realpath "$5"); gen=$(realpath "$6"); sep=$(realpath "$7"); op=$(realpath "$8"); base=$(realpath "$9"); out=$(realpath -m "${10}")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 5ad2b30ed5f90057b5cddb40dfd00827f19ea6569a16fdb678b686296147b26d "$src/PA194TermFreeBound.lean" \
 6cb924c2b23249d0cd808ab7d1e49691e251ac9662980e873e3439f3c9364948 "$src/PA194FormulaFreeBound.lean" \
 54ba9152a5047eb3e3cab294717db44e2464e2e3f123d84ba35283408ee4746a "$src/PA194FreeBoundBind.lean" \
 1986c5f445142eda693321d9e45e92fda3db79ca06e37485c45025e78324760f "$src/PA194FormulaFreeBoundBind.lean" \
 9e019fffa3289a06b1c475872b413d55b5522b9a7a53d162e90bfbf380ad5f04 "$src/PA194FreeBoundIteration.lean" \
 818245a5ea913263aae512d7e33535e57dbc66e63984f6d39162a0537d1a42b8 "$src/PA194FreeBoundClosed.lean" \
 6f595e41db0fa42f9576e9b5bbb83b30611dbdc87c154af0e9717c0cb58a2f09 "$src/PA194FullyClosedSeparation.lean" \
 b58a7dbaf43735a8d2aac6b39b48479963e097e7d48b09a4b3b2fa750fe10582 "$src/PA194FullyClosedAudit.lean" \
 932ffc2cfee03623c85083d5529298327888895d08df0c1512116991878f9a73 "$fullsep/PA194ModelClosureComplexity.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$fullsep:$seeded:$df:$closure:$gen:$sep:$op:/dev/shm/pa194-adjunctive-admission-audit:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194TermFreeBound PA194FormulaFreeBound PA194FreeBoundBind PA194FormulaFreeBoundBind PA194FreeBoundIteration PA194FreeBoundClosed PA194FullyClosedSeparation PA194FullyClosedAudit; do
 echo "Checking $n"
 lean -j1 -M 4000 -R "$src" -o "$out/$n.olean" "$src/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194FullyClosedAudit.log") == 12 ]]
cat "$out/PA194FullyClosedAudit.log"
check_inputs
echo 'PASS: model-level fully closed parameterized separation leaf; staged dependencies prebuilt.'
