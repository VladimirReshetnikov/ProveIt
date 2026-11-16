#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

repo=$(cd -- "${1:?repository root required}" && pwd)
native=$(cd -- "${2:?checked literal endpoint stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
native_module=${4:-PA194NativeLiteralFinal}
source=${5:-"$here/PA194NativeLiteralConcise.lean"}
source_dir=$(cd -- "$(dirname -- "$source")" && pwd)
module=$(basename -- "$source" .lean)
source="$source_dir/$module.lean"
test -s "$source"
test -s "$native/$native_module.olean"
test -s "$native/leanpath.txt"
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
bridge_leanpath=$(lake env printenv LEAN_PATH)

# Keep the literal replay's provider order when supplying the additional
# bridge dependencies. Rebuild the syntax and standard bridge in that order.
LEAN_PATH="$(python3 -I - "$out" "$native" "$bridge_leanpath" <<'PY'
from pathlib import Path
import sys

out, native, bridge = sys.argv[1:]
native_paths = (Path(native) / "leanpath.txt").read_text().strip().split(":")
paths = dict.fromkeys(p for p in [native, *native_paths, *bridge.split(":")] if p)
for namespace in ("DiophantineConsistency", "IPRABridge"):
    overlay = Path(out) / namespace
    for path in paths:
        provider = Path(path) / namespace
        for source in provider.rglob("*.olean"):
            relative = source.relative_to(provider)
            if namespace == "IPRABridge" and relative in {
                    Path("Syntax.olean"), Path("ReferenceAxiomImages.olean"), Path("Standard.olean")}:
                continue
            target = overlay / relative
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

bridge_source="$repo/Logic/PrimitiveRecursiveArithmetic/Bridge/Lean"
mkdir -p "$out/IPRABridge"
bash "$here/prepare-bridge-syntax.sh" "$out"
for bridge_module in Syntax ReferenceAxiomImages Standard; do
  if ! lean -j1 -M6000 -R "$bridge_source" -o "$out/IPRABridge/$bridge_module.olean" \
      "$bridge_source/IPRABridge/$bridge_module.lean" >>"$out/bridge.log" 2>&1; then
    cat "$out/bridge.log"
    exit 1
  fi
done

log="$out/$module.log"
if ! lean -j1 -M6000 -R "$source_dir" -o "$out/$module.olean" "$source" >"$log" 2>&1; then
  cat "$log"
  exit 1
fi
cat "$log"
if rg -q "error[:(]|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
tr -s '[:space:]' ' ' <"$log" |
  rg -F "'$module.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" >/dev/null
sha256sum "$source" "$native/$native_module.olean" "$out/$module.olean" \
  "$bridge_source/IPRABridge/"{Syntax,ReferenceAxiomImages,Standard}.lean \
  "$out/IPRABridge/"{Syntax,ReferenceAxiomImages,Standard}.olean \
  "$out/DiophantineConsistency/"{PRAFiniteCodeSyntax,IPRAOpenSyntax,IPRAReferenceLanguage}.olean \
  "$out/DiophantineConsistency/IPRAStandardTheory.olean" >"$out/sha256.txt"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
