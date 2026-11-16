#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

repo=$(cd -- "${1:?repository root required}" && pwd)
core=$(cd -- "${2:?checked constructor model stage required}" && pwd)
out=${3:?fresh output directory required}
coefficient=${4:-5}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
case $coefficient in
  5|6) ;;
  *) printf 'Expected coefficient 5 or 6\n' >&2; exit 2 ;;
esac
module="PA194M${coefficient}ConsSites"
test -f "$core/PA194ProgramCons.olean"
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$core:$(cat "$core/leanpath.txt")"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
python3 -I "$here/generate-cons-sites.py" "$repo" "$out" "$coefficient"

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
check "$module" "$out/$module.lean"
rg -Fxq "'PA194ProgramCons.Certified.rows' depends on axioms: [propext, Quot.sound]" "$out/PA194ProgramConsCertificate.log"
rg -Fxq "'PA194ProgramCons.CertifiedSlice.certified' depends on axioms: [propext, Quot.sound]" "$out/PA194ProgramConsCertificate.log"
rg -Fxq "'$module.checked' depends on axioms: [propext]" "$out/$module.log"
rg -Fxq "'$module.constructors' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/$module.log"
sha256sum "$here/PA194ProgramConsCertificate.lean" "$here/generate-cons-sites.py" "$here/check-cons-sites.sh" \
  "$out/$module.lean" "$out"/*.olean > "$out/sha256.txt"
