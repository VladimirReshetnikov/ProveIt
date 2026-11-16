#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

recoding=$(cd -- "${1:?checked radix recoding stage required}" && pwd)
rho8=$(cd -- "${2:?checked restricted implication stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)

export LEAN_PATH="$(python3 -I - "$out" "$recoding" "$rho8" <<'PY'
from pathlib import Path
import sys

out, *stages = sys.argv[1:]
paths = [out, *stages]
for stage in stages:
    paths.extend((Path(stage) / 'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(p for p in paths if p)))
PY
)"
modules=(PA194M5RecodeConstructors PA194M5RecodeHeads PA194M5ProofTransport)
sources=()
for module in "${modules[@]}"; do
  source="$here/$module.lean"
  log="$out/$module.log"
  sources+=("$source")
  if ! lean -j1 -M5000 -R "$here" -o "$out/$module.olean" "$source" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
done
for theorem in proofTransport refutationTransport; do
  rg -Fxq "'PA194M5ProofTransport.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$out/PA194M5ProofTransport.log"
done
sha256sum "${sources[@]}" "$here/check-radix-transport.sh" "$out"/*.olean >"$out/sha256.txt"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
