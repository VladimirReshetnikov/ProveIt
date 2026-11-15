#!/usr/bin/env bash
set -euo pipefail
if (($# != 12)); then echo 'usage: REPO BASELINE CARRY_STAGE DYNAMIC_CODE_STAGE ROUND_STAGE SEED_STAGE FINISH_STAGE DYNAMIC28_STAGE PROJECT PACKAGE CLOCK_SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); codes=$(realpath "$4"); round=$(realpath "$5"); seed=$(realpath "$6"); finish=$(realpath "$7"); complete=$(realpath "$8"); project=$(realpath "$9"); package=$(realpath "${10}"); source=$(realpath "${11}"); out="${12}"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
check() {
 printf '%s  %s\n' \
 bf325c6583c582161ded1ef274fd64cba238c70f932b8c3425d807396ffec4c5 "$source/PA194Site28DynamicClock.lean" \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 70105c2463768da42439b8365e1798209d16d814d11d125c1c6cbeac8f48327a "$codes/PA194OneSpareFileRoundTrip.olean" \
 f739d7761eee43bcb1ce3633792d8b480da5872bca616d73d274cf21735abeea "$round/PA194Site28CarryRoundTrip.olean" \
 ad9dda641b3c8fe1ef1280d22e436c8b321bddeeae2f55900f4f7a72cb4ea35e "$seed/PA194Site28SeedRoundTrip.olean" \
 a37aaeb8672213339812ae37fc74def23ddb907955d516f4fdeaef2ddc32e666 "$finish/PA194Site28FinishReturn.olean" \
 dea551883f4af37c1d40c45fe5c230d37d22eeb16a7752cb42b9a14452004ef1 "$source/dynamic-stage-receipt.json" | sha256sum -c -
 python3 - "$complete" "$source/dynamic-stage-receipt.json" <<'PY'
import hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1]); receipt=json.loads(pathlib.Path(sys.argv[2]).read_text())
record=receipt.get(str(root))
if record is None: raise SystemExit('stage path absent from receipt')
files={p.name for p in root.glob('*.olean')}
if files != set(record): raise SystemExit('stage object set changed')
for name,h in record.items():
 if hashlib.sha256((root/name).read_bytes()).hexdigest()!=h: raise SystemExit('stage object changed: '+name)
print('Dynamic-28 staged object receipt OK')
PY
}
check
mkdir -p "$out"; out=$(realpath "$out")
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$complete:$finish:$seed:$round:$codes:$stage:$baseline:$project:$package:$lake_path"
lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -R "$source" -o "$out/PA194Site28DynamicClock.olean" "$source/PA194Site28DynamicClock.lean" > "$out/PA194Site28DynamicClock.log" 2>&1
rg -q "^'PA194Site28DynamicClock.exactClock' depends on axioms:" "$out/PA194Site28DynamicClock.log"
if rg -q 'sorryAx|declaration uses .sorry.' "$out/PA194Site28DynamicClock.log"; then cat "$out/PA194Site28DynamicClock.log"; exit 1; fi
rg 'depends on axioms:' "$out/PA194Site28DynamicClock.log"
check
echo 'PASS: exact dynamic site-28 model clock; staged machine and general foundations remain prebuilt.'
