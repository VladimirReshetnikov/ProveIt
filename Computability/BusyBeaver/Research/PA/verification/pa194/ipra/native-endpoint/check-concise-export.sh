#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

repo=$(cd -- "${1:?repository root required}" && pwd)
native=$(cd -- "${2:?checked literal PA194 endpoint stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test -s "$native/PA194NativeLiteralFinal.olean"
test -s "$native/leanpath.txt"
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
bridge_leanpath=$(lake env printenv LEAN_PATH)

# Lean selects the first directory for a namespace. Expose one namespace with
# the literal replay's modules first and the additional bridge dependencies after them.
LEAN_PATH="$(python3 -I - "$out" "$native" "$bridge_leanpath" <<'PY'
from pathlib import Path
import sys

out, native, bridge = sys.argv[1:]
native_paths = (Path(native) / "leanpath.txt").read_text().strip().split(":")
paths = dict.fromkeys(p for p in [native, *native_paths, *bridge.split(":")] if p)
namespace = "DiophantineConsistency"
overlay = Path(out) / namespace
for path in paths:
    provider = Path(path) / namespace
    for source in provider.rglob("*.olean"):
        target = overlay / source.relative_to(provider)
        if target.exists() or not source.is_file():
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        for suffix in ("", ".private", ".server"):
            artifact = Path(f"{source}{suffix}")
            if artifact.is_file():
                Path(f"{target}{suffix}").symlink_to(artifact.absolute())

print(":".join(dict.fromkeys([out, *paths])))
PY
)"
export LEAN_PATH

module=PA194NativeLiteralConcise
log="$out/$module.log"
if ! lean -j1 -M6000 -R "$here" -o "$out/$module.olean" "$here/$module.lean" >"$log" 2>&1; then
  cat "$log"
  exit 1
fi
cat "$log"
if rg -q "error[:(]|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
tr -s '[:space:]' ' ' <"$log" |
  rg -F "'$module.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" >/dev/null
sha256sum "$here/$module.lean" "$native/PA194NativeLiteralFinal.olean" "$out/$module.olean" >"$out/sha256.txt"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
