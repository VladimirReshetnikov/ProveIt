#!/usr/bin/env bash
# FUTURE VALIDATION HARNESS; Lean was unavailable in the preparation environment.
# Requires a full clean pinned checkout with dependencies and baseline already built.
# Does not call git clone/fetch, lake build/update, cache, elan, or any installer.
# Only generated sources, .olean outputs and logs under OUT are written.
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0 GIT_TERMINAL_PROMPT=0
PIN=60e9c5d620c6c387d932876cfa2d9376f64ea56c
BUNDLE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
unavailable() { printf 'UNAVAILABLE: %s\n' "$*" >&2; exit 69; }
fail() { printf 'FAILED: %s\n' "$*" >&2; exit 1; }
if [[ $# -lt 2 || $# -gt 3 ]]; then
  printf 'Usage: %s FULL_PROVEIT_CHECKOUT DIRECT_TOOLCHAIN_BIN [NEW_OUTPUT_DIRECTORY]\n' "$0" >&2
  printf 'DIRECT_TOOLCHAIN_BIN must contain existing Lean 4.32.0 lean and lake binaries, not elan shims.\n' >&2
  exit 64
fi
ROOT=$1
BIN=$2
[[ -x "$BIN/lean" && -x "$BIN/lake" ]] || unavailable 'existing direct lean and lake binaries are required; no installation attempted'
BIN=$(cd -- "$BIN" && pwd -P)
for executable in lean lake; do
  resolved=$(readlink -f -- "$BIN/$executable")
  [[ ${resolved##*/} != elan ]] || unavailable "$BIN/$executable is an elan shim; use the installed toolchain bin directory"
done
command -v python3 >/dev/null || unavailable 'python3 is required for log validation'
command -v git >/dev/null || unavailable 'git is required for the immutable checkout preflight'
[[ -d "$ROOT" ]] || unavailable 'full checkout directory is absent'
ROOT=$(cd -- "$ROOT" && pwd -P)
[[ $(git -C "$ROOT" rev-parse HEAD 2>/dev/null) == "$PIN" ]] || fail "checkout HEAD must equal $PIN"
git -C "$ROOT" --no-pager diff --no-ext-diff --quiet HEAD -- || fail 'tracked checkout differs from pinned HEAD; use a clean disposable checkout'
[[ $(tr -d '\r\n' < "$ROOT/lean-toolchain") == leanprover/lean4:v4.32.0 ]] || fail 'unexpected toolchain pin'
VERSION=$("$BIN/lean" --version)
[[ "$VERSION" =~ version\ 4\.32\.0([,\ ]|$) ]] || fail "unexpected compiler version: $VERSION"
[[ -f "$ROOT/lakefile.toml" && -f "$ROOT/lake-manifest.json" ]] || unavailable 'full root build configuration is absent'
[[ -f "$ROOT/.lake/build/lib/lean/DiophantineConsistency.olean" ]] || unavailable 'baseline DiophantineConsistency.olean is absent; authorized baseline build is a prerequisite'
[[ -f "$ROOT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]] || unavailable 'prebuilt Mathlib.olean needed by PortableCandidates is absent'
# Refuse obvious incomplete dependencies before asking Lake for its environment.
python3 - "$ROOT" <<'PY' || unavailable 'locked dependency directories are incomplete; no installation attempted'
import json,sys
from pathlib import Path
root=Path(sys.argv[1]); d=json.loads((root/'lake-manifest.json').read_text())
base=root/d.get('packagesDir','.lake/packages')
missing=[str(base/p['name']) for p in d.get('packages',[]) if not (base/p['name']).is_dir()]
if missing:
    print('Missing locked package directories: '+', '.join(missing), file=sys.stderr)
    raise SystemExit(1)
PY
if [[ $# == 3 ]]; then
  OUT=$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve())' "$3")
  case "$OUT/" in "$ROOT/"*) fail 'output directory must be outside the checkout';; esac
  [[ ! -e "$OUT" ]] || fail 'output directory must be new (avoid overwriting evidence)'
  mkdir -p -- "$OUT"
else
  TMPBASE=$(cd -- "${TMPDIR:-/tmp}" && pwd -P)
  case "$TMPBASE/" in "$ROOT/"*) unavailable 'temporary directory is inside checkout; provide a new external output directory';; esac
  OUT=$(mktemp -d "$TMPBASE/proveit-simplification-replay.XXXXXXXX")
fi
mkdir -p -- "$OUT/logs" "$OUT/src/shared" "$OUT/olean/shared"
printf '%s\n' "$PIN" > "$OUT/commit.txt"
printf '%s\n' "$VERSION" > "$OUT/lean-version.txt"
printf 'NOT_COMPLETED\n' > "$OUT/STATUS"
printf 'Outputs: %s\n' "$OUT"
: > "$OUT/all-axioms.log"
: > "$OUT/expected-all.txt"

replay_one() {
  local relative=$1 module=$2 group=$3
  local source="$BUNDLE/$relative" srcroot="$OUT/src/$group" libroot="$OUT/olean/$group"
  local modulepath=${module//./\/}
  local src="$srcroot/$modulepath.lean" object="$libroot/$modulepath.olean"
  local log="$OUT/logs/${group}_${module//./_}.log" expected="$OUT/logs/${group}_${module//./_}.expected.txt"
  [[ -f "$source" ]] || fail "missing proposal artifact: $relative"
  mkdir -p -- "$(dirname -- "$src")" "$(dirname -- "$object")"
  cp -- "$source" "$src"
  python3 - "$src" "$expected" <<'PY'
import re,sys
from pathlib import Path
s=Path(sys.argv[1]).read_text()
names=re.findall(r'^#print\s+axioms\s+(\S+)\s*$',s,re.M)
if not names: raise SystemExit('No explicit expected audit targets; refusing vacuous replay')
Path(sys.argv[2]).write_text('\n'.join(names)+'\n')
PY
  # The expansion of LEAN_PATH occurs INSIDE `lake env`, after Lake has supplied
  # its dependency path. Never replace it with the calling shell's empty value.
  # Each API-preserving replacement has its own output world, so it cannot
  # accidentally shadow baseline Steps modules in unrelated candidate probes.
  if (cd -- "$ROOT" && "$BIN/lake" env bash --noprofile --norc -c '
      export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
      shift
      exec "$@"
    ' replay "$libroot" "$BIN/lean" --root="$srcroot" -o "$object" "$src") > "$log" 2>&1; then
    printf 'compiler_exit=0\n' > "$log.exit"
  else
    local rc=$?
    printf 'compiler_exit=%s\n' "$rc" > "$log.exit"
    printf 'FAILED_COMPILATION %s\n' "$relative" > "$OUT/STATUS"
    cat -- "$log" >&2
    fail "Lean rejected $relative (exit $rc); log retained: $log"
  fi
  if ! python3 "$BUNDLE/validation/check_axiom_log.py" "$log" --expected "$expected" > "$log.axioms.json"; then
    printf 'FAILED_AXIOM_POLICY %s\n' "$relative" > "$OUT/STATUS"
    cat -- "$log.axioms.json" >&2
    fail "axiom policy rejected $relative"
  fi
  cat -- "$log" >> "$OUT/all-axioms.log"
  printf '\n' >> "$OUT/all-axioms.log"
  cat -- "$expected" >> "$OUT/expected-all.txt"
  printf 'Candidate elaboration and selected axiom gate passed: %s\n' "$relative"
}

# Dependency ordering is essential: compatibility imports the generated generic olean.
replay_one architecture/NineCoordinatePackaging.lean NineCoordinatePackaging shared
replay_one architecture/NineCoordinatePackagingCompatibility.lean NineCoordinatePackagingCompatibility shared
replay_one tactics/PortableCandidates.lean PortableCandidates shared
replay_one tactics/SourceCandidates.lean SourceCandidates shared
replay_one circuits/SplitCircuitCandidate59.lean SplitCircuitCandidate59 shared
replay_one circuits/GapCircuitCandidate66.lean GapCircuitCandidate66 shared
replay_one circuits/api_preserving_candidates/DiophantineConsistency/SplitCircuitSteps59.lean DiophantineConsistency.SplitCircuitSteps59 api_split
replay_one circuits/api_preserving_candidates/DiophantineConsistency/GapCircuitSteps66.lean DiophantineConsistency.GapCircuitSteps66 api_gap
replay_one validation/EndpointAudit.lean EndpointAudit shared
python3 "$BUNDLE/validation/check_axiom_log.py" "$OUT/all-axioms.log" --expected "$OUT/expected-all.txt" > "$OUT/combined-axiom-policy.json"
python3 - "$OUT" <<'PY'
import hashlib,json,sys
from pathlib import Path
root=Path(sys.argv[1]); files=sorted((root/'src').rglob('*.lean'))
(root/'replayed-source-sha256.json').write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},indent=2)+'\n')
PY
printf 'CANDIDATE_ELABORATION_AND_SELECTED_AXIOMS_PASSED\nNOT_A_FULL_INTEGRATION_BUILD\n' > "$OUT/STATUS"
printf 'All candidate probes passed. This is NOT a downstream migration or full project regression pass. Evidence: %s\n' "$OUT"
