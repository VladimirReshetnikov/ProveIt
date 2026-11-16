#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

repo=$(cd -- "${1:?repository root required}" && pwd)
core=$(cd -- "${2:?checked constructor model stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test -f "$core/PA194ProgramCons.olean"
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$core:$(cat "$core/leanpath.txt")"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
python3 -I "$here/generate-cons-sites.py" "$repo" "$out"

check() {
  local module=$1 source=$2
  local log="$out/$module.log"
  if ! lean -j1 -M5000 -R "$(dirname -- "$source")" -o "$out/$module.olean" "$source" > "$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
  printf 'PASS %s\n' "$module"
}
check PA194ProgramConsCertificate "$here/PA194ProgramConsCertificate.lean"
check PA194M5ConsSites "$out/PA194M5ConsSites.lean"
rg -Fxq "'PA194ProgramCons.Certified.rows' depends on axioms: [propext, Quot.sound]" "$out/PA194ProgramConsCertificate.log"
rg -Fxq "'PA194ProgramCons.CertifiedSlice.certified' depends on axioms: [propext, Quot.sound]" "$out/PA194ProgramConsCertificate.log"
rg -Fxq "'PA194M5ConsSites.checked' depends on axioms: [propext]" "$out/PA194M5ConsSites.log"
rg -Fxq "'PA194M5ConsSites.constructors' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194M5ConsSites.log"
sha256sum "$here/PA194ProgramConsCertificate.lean" "$here/generate-cons-sites.py" "$here/check-cons-sites.sh" \
  "$out/PA194M5ConsSites.lean" "$out"/*.olean > "$out/sha256.txt"
