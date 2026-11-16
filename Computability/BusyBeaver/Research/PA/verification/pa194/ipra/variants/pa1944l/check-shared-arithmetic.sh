#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
model=$(cd -- "${1:?checked PA1944L model stage required}" && pwd)
coverage=$(cd -- "${2:?checked PA1944L coverage stage required}" && pwd)
out=${3:?fresh output directory required}
current=$(cd -- "${4:-$repo/.lake/build/lib/lean}" && pwd)
test ! -e "$out"
mkdir -p "$out/providers"
out=$(cd -- "$out" && pwd)
cd "$repo"

# Select the current declaration and proof modules together. Retain the
# checked machine providers and their order for the rest of the replay.
python3 -I - "$out/providers" "$model" "$coverage" "$current" "$(lake env printenv LEAN_PATH)" <<'PY'
from hashlib import sha256
from pathlib import Path
from shutil import copy2
import sys

out, model, coverage, current, workspace_path = sys.argv[1:]
out = Path(out)
namespace = "DiophantineConsistency"
current = Path(current)
latest = (
    "IPRAStandardAxioms", "IPRAStandardTheory", "IPRAArithmeticTerms",
    "IPRAArithmeticInstantiation", "IPRASuccessorInduction",
    "IPRASuccessorInductionConverse", "IPRAAddOneGeneral",
    "SubSuccSelfNonzeroSyntax", "IPRASubSuccSelfNonzero", "IPRADifferenceSuccEq",
    "IPRADifferenceSuccLogic", "IPRADifferenceStepClosure",
)
legacy = [p for stage in (coverage, model) for p in
          (Path(stage) / "leanpath.txt").read_text().strip().split(":") if p]
paths = dict.fromkeys([out, *map(Path, legacy), current, *map(Path, workspace_path.split(":"))])

def place(source, target, snapshot=False):
    target.parent.mkdir(parents=True, exist_ok=True)
    for suffix in ("", ".private", ".server"):
        artifact = Path(f"{source}{suffix}")
        if artifact.is_file():
            dest = Path(f"{target}{suffix}")
            if snapshot:
                copy2(artifact, dest)
            else:
                dest.symlink_to(artifact.resolve())

with (out / "sha256.txt").open("w") as receipt:
    selected = [current / namespace / f"{module}.olean" for module in latest]
    for package in ("IPRABridge", "IPRADerivations", "ConciseIPRA"):
        provider = current / package
        selected.extend(sorted(source for source in provider.rglob("*.olean")
                               if source.relative_to(provider).parts[0] != "Checks"))
    for source in selected:
        target = out / source.relative_to(current)
        place(source, target, snapshot=True)
        digest = sha256(target.read_bytes()).hexdigest()
        receipt.write(f"{digest}  {target}\n")
for path in list(paths)[1:]:
    provider = path / namespace
    for source in provider.rglob("*.olean"):
        target = out / namespace / source.relative_to(provider)
        if not target.exists() and source.is_file():
            place(source, target)
(out / "leanpath.txt").write_text(":".join(map(str, paths)) + "\n")
PY

LEAN_PATH=$(cat "$out/providers/leanpath.txt") \
  bash "$here/../../native-endpoint/prepare-bridge-syntax.sh" "$out/providers"
sha256sum "$out/providers/DiophantineConsistency/"{PRAFiniteCodeSyntax,IPRAOpenSyntax,IPRAReferenceLanguage}.olean \
  >>"$out/providers/sha256.txt"

bash "$here/../check-controller-final.sh" PA1944L "$model" "$out/providers" "$out/native"
export LEAN_PATH=$(cat "$out/native/leanpath.txt")
if ! lean -j1 -M6000 --run "$here/PA1944LSharedArithmeticChecks.lean" >"$out/proof-path.log" 2>&1; then
  cat "$out/proof-path.log"
  exit 1
fi
cat "$out/proof-path.log"
bash "$here/check-concise-export.sh" "$out/native" "$out/concise"
sha256sum -c --quiet "$out/providers/sha256.txt"
