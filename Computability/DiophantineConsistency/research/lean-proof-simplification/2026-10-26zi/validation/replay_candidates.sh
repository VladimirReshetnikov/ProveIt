#!/usr/bin/env bash
# FUTURE REPLAY ONLY. Adapted support, not a new simplification recommendation.
# Requires a complete clean pinned DISPOSABLE checkout and prebuilt dependencies.
# Never installs, updates, fetches or invokes `lake build`; generated candidate
# sources/oleans/logs are isolated under OUT. Lake may read/init its local metadata.
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0 GIT_TERMINAL_PROMPT=0
PIN=e652d21c413de59e4821f6e8e9b6a3a077bf5bfe
BUNDLE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
unavailable() { printf 'UNAVAILABLE: %s\n' "$*" >&2; exit 69; }
fail() { printf 'FAILED: %s\n' "$*" >&2; exit 1; }
if [[ $# -lt 2 || $# -gt 3 ]]; then
  printf 'Usage: %s FULL_PINNED_DISPOSABLE_CHECKOUT DIRECT_TOOLCHAIN_BIN [NEW_EXTERNAL_OUTPUT_DIR]\n' "$0" >&2
  exit 64
fi
ROOT=$1 BIN=$2
[[ -x "$BIN/lean" && -x "$BIN/lake" ]] || unavailable 'existing direct Lean/Lake binaries required; no installation attempted'
BIN=$(cd -- "$BIN" && pwd -P)
for executable in lean lake; do
  resolved=$(readlink -f -- "$BIN/$executable")
  [[ ${resolved##*/} != elan ]] || unavailable "$BIN/$executable is an elan shim; use installed toolchain/bin"
done
command -v python3 >/dev/null || unavailable 'python3 required'
command -v git >/dev/null || unavailable 'git required'
[[ -d "$ROOT" ]] || unavailable 'full checkout absent'
ROOT=$(cd -- "$ROOT" && pwd -P)
case "$ROOT/" in "$BUNDLE/"*) fail 'do not use the selected source snapshot as a checkout';; esac
[[ $(git -C "$ROOT" rev-parse HEAD 2>/dev/null) == "$PIN" ]] || fail "HEAD must equal $PIN"
git -C "$ROOT" --no-pager diff --no-ext-diff --quiet HEAD -- || fail 'tracked sources differ from pinned HEAD'
[[ $(tr -d '\r\n' < "$ROOT/lean-toolchain") == leanprover/lean4:v4.32.0 ]] || fail 'unexpected toolchain pin'
VERSION=$("$BIN/lean" --version)
[[ "$VERSION" =~ version\ 4\.32\.0([,\ ]|$) ]] || fail "wrong compiler: $VERSION"
[[ -f "$ROOT/lakefile.toml" && -f "$ROOT/lake-manifest.json" ]] || unavailable 'root Lake configuration absent'
# Validate nonempty ordered plan, all public candidate audit targets, and
# prebuilt import/dependency availability BEFORE making any output directory.
python3 "$BUNDLE/validation/plan_tools.py" >/dev/null || fail 'invalid replay plan'
python3 - "$ROOT" "$BUNDLE" <<'PY' || unavailable 'prebuilt imports or locked dependencies absent; no build/install attempted'
import json,sys
from pathlib import Path
root,bundle=map(Path,sys.argv[1:]); sys.path.insert(0,str(bundle/'validation'))
from plan_tools import inspect_plan
plan=inspect_plan(json.loads((bundle/'validation/replay_plan.json').read_text()),bundle)
m=json.loads((root/'lake-manifest.json').read_text()); base=root/m.get('packagesDir','.lake/packages')
packages=[base/p['name'] for p in m.get('packages',[])]
missing=[str(p) for p in packages if not p.is_dir()]
libs=[root/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in packages]
overlay={p['module'] for p in plan['probes']}
for name in {n for p in plan['probes'] for n in p['imports']}-overlay:
    relative=Path(*name.split('.')).with_suffix('.olean')
    if not any((lib/relative).is_file() for lib in libs): missing.append(name+' (prebuilt .olean)')
if missing: print('\n'.join(missing),file=sys.stderr);raise SystemExit(1)
PY
if [[ $# == 3 ]]; then
  OUT=$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve())' "$3")
  case "$OUT/" in "$ROOT/"*|"$BUNDLE/"*) fail 'OUT must be outside checkout and review bundle';; esac
  [[ ! -e "$OUT" ]] || fail 'OUT must be new; do not overwrite evidence'
  mkdir -p -- "$OUT"
else
  TMPBASE=$(cd -- "${TMPDIR:-/tmp}" && pwd -P)
  case "$TMPBASE/" in "$ROOT/"*|"$BUNDLE/"*) fail 'supply a new external output directory';; esac
  OUT=$(mktemp -d "$TMPBASE/proveit-round4-replay.XXXXXXXX")
fi
mkdir -p -- "$OUT/logs" "$OUT/src" "$OUT/olean"
printf '%s\n' "$PIN" > "$OUT/commit.txt"
printf '%s\n' "$VERSION" > "$OUT/lean-version.txt"
printf 'NOT_COMPLETED\n' > "$OUT/STATUS"
cp -- "$BUNDLE/validation/replay_plan.json" "$OUT/replay_plan.json"
python3 "$BUNDLE/validation/plan_tools.py" --tsv --expected "$OUT/expected-all.txt" --prerequisites "$OUT/import-prerequisites.txt" > "$OUT/replay-order.tsv"
: > "$OUT/all-axioms.log"
python3 - "$ROOT" "$OUT" "$BUNDLE" <<'PYHASH'
import hashlib,json,sys
from pathlib import Path
root,out,bundle=map(Path,sys.argv[1:]);m=json.loads((root/'lake-manifest.json').read_text())
base=root/m.get('packagesDir','.lake/packages');libs=[root/'.lake/build/lib/lean']+[base/p['name']/'.lake/build/lib/lean' for p in m.get('packages',[])]
sys.path.insert(0,str(bundle/'validation'));from plan_tools import inspect_plan
plan=inspect_plan(json.loads((bundle/'validation/replay_plan.json').read_text()),bundle)
files=[root/'lean-toolchain',root/'lake-manifest.json',root/'lakefile.toml']
overlay={p['module'] for p in plan['probes']}
for name in {n for p in plan['probes'] for n in p['imports']}-overlay:
    rel=Path(*name.split('.')).with_suffix('.olean')
    files.append(next(lib/rel for lib in libs if (lib/rel).is_file()))
(out/'baseline-import-and-config-sha256.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},indent=2)+'\n')
PYHASH
printf 'Outputs: %s\n' "$OUT"
while IFS=$'\t' read -r relative module group; do
  srcroot="$OUT/src/$group" libroot="$OUT/olean/$group" modulepath=${module//./\/}
  src="$srcroot/$modulepath.lean" object="$libroot/$modulepath.olean"
  log="$OUT/logs/${group}_${module//./_}.log"
  mkdir -p -- "$(dirname -- "$src")" "$(dirname -- "$object")"
  cp -- "$BUNDLE/$relative" "$src"
  python3 - "$BUNDLE" "$relative" "$log.expected.txt" <<'PY'
import json,sys
from pathlib import Path
bundle,relative,out=sys.argv[1:]
p=next(p for p in json.loads((Path(bundle)/'validation/replay_plan.json').read_text())['probes'] if p['source']==relative)
Path(out).write_text('\n'.join(p['expected'])+'\n')
PY
  # Expand LEAN_PATH inside Lake's environment, not before it. One
  # ordered world composes all candidates and unchanged connector modules.
  if (cd -- "$ROOT" && "$BIN/lake" env bash --noprofile --norc -c '
      export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
      shift
      exec "$@"
    ' replay "$libroot" "$BIN/lean" --root="$srcroot" -o "$object" "$src") > "$log" 2>&1; then
    printf 'compiler_exit=0\n' > "$log.exit"
  else
    rc=$?; printf 'compiler_exit=%s\n' "$rc" > "$log.exit"
    printf 'FAILED_COMPILATION %s\n' "$relative" > "$OUT/STATUS"
    cat -- "$log" >&2; fail "Lean rejected $relative; retained $log"
  fi
  if ! python3 "$BUNDLE/validation/check_axiom_log.py" "$log" --expected "$log.expected.txt" > "$log.axioms.json"; then
    printf 'FAILED_AXIOM_POLICY %s\n' "$relative" > "$OUT/STATUS"
    cat -- "$log.axioms.json" >&2; fail "axiom log policy rejected $relative"
  fi
  cat -- "$log" >> "$OUT/all-axioms.log"; printf '\n' >> "$OUT/all-axioms.log"
  printf 'Candidate and selected axiom gate passed: %s\n' "$relative"
done < "$OUT/replay-order.tsv"
python3 "$BUNDLE/validation/check_axiom_log.py" "$OUT/all-axioms.log" --expected "$OUT/expected-all.txt" > "$OUT/combined-axiom-policy.json"
python3 - "$OUT" <<'PY'
import hashlib,json,sys
from pathlib import Path
root=Path(sys.argv[1]); files=sorted((root/'src').rglob('*.lean'))
(root/'replayed-source-sha256.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},indent=2)+'\n')
PY
git -C "$ROOT" --no-pager diff --no-ext-diff --quiet HEAD -- || fail 'tracked checkout changed during replay; inspect before trusting outputs'
printf 'CANDIDATE_ELABORATION_AND_SELECTED_AXIOMS_PASSED\nNOT_A_FULL_INTEGRATION_BUILD\n' > "$OUT/STATUS"
printf 'All selected candidate probes passed; NOT a downstream integration or project regression result. Evidence: %s\n' "$OUT"
