#!/usr/bin/env bash
set -euo pipefail
if (($# != 6)); then
  echo "usage: $0 REPO FETCH_SOURCE_DIR PROJECT_FOUNDATION PACKAGE_FOUNDATION GRAPH_NAMESPACE NEW_OUTPUT" >&2
  exit 2
fi
repo=$(realpath "$1")
src=$(realpath "$2")
project=$(realpath "$3")
package=$(realpath "$4")
graph=$(realpath "$5")
out=$(realpath -m "$6")
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Output must not already exist' >&2; exit 2; }
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  2654808e5cfba0266f38ce2ddad33987635e8e06c3934cc131eb2a475bc1eeae "$graph/PRAHistoryResultGraph.olean" \
  4b3ea00b4fbf5790008bddc61a69d2b7bdf84551e67084219014b57bd6402db2 "$graph/PRAHistoryTrace.olean" \
  b359da5684d709684b25fcd7c7073804a91044fc54ae0f2bfc9b44a7b1844583 "$graph/PRAHistoryIterator.olean" \
  e976a9cc5de9e9ca257f78e16ea444a32684ecc3cb74f4c8f0bef7fabbb1ce40 "$graph/PRAHistorySingletonSequence.olean" \
  85aeb8494921b2211b7c4ca01b0fce4b5153ce0839ad6bc5e087dfdbb047c45d "$graph/PRAHistorySingletonMembership.olean" \
  d225bca0cd681778109ef906169e7f7a0549289635c81e2a987f3cd67aab1c58 "$graph/PRAHistoryLengthUnique.olean" \
  ff2086387bc3de5a2843bdb7b13ca72b1cd2e2c65866125b4de8610cb40c23f6 "$src/PA194SchedulerFetchPositive.lean" \
  24d3b73bb21939d35a06967703c761b9f0b8b5b2166efc1af0fd1caf837baee8 "$src/PA194SchedulerPackedFetchPositive.lean" \
  a6ff98751ef52efd5969f002536920e749917ded437806bddbf08f96719b69ca "$src/PA194SchedulerFetchFresh.lean" \
  bcdf965a454fa001035e87ae87d7ce0beb36a30a238ab5ef4f1062a394bdb758 "$src/PA194SourceFetchLoop.lean" \
  46b91b25d30fb9994b1e96ca3387271d9d4a1c620c1072a84b47c7cf93a7ebb3 "$src/PA194ControllerRunAdd.lean" \
  af2ce076f3a3c6a409d8a7c38be9ec116e23e051d7d022137a39119aa7f8d124 "$src/PA194SourceDrainInvariant.lean" \
  9cbb711b6ad2fa062f09d2da9b8eb42fc8499c691e932f1b1f1020f40f0f4840 "$src/PA194SourceDrainModel.lean" \
  8d433af8e2f225e17a1dcb1f4f7627c02198686686065dc4f2caff56c8eeec5b "$src/PA194SourceFetchRestoreLoop.lean" \
  bef3aecfd951d0890ddc6b3197edbc47366480f73233a909ceed1f3ddd211912 "$src/PA194SourceRestoreInvariant.lean" \
  24d4e62276ade2604d7a1f8c92016cad103331f392f42ea4e93905fa22efb87a "$src/PA194SourceRestoreModel.lean" \
  8b5faab3fbeeaa96dae06c69244581e0af6182d89f965bde9db80e41d60dca97 "$src/PA194SourceFetchModel.lean" \
  3428d3bbb0a49768898fb3c4e408a5e1bde07aeed8412f531ad069ef459713bf "$src/PA194SchedulerFetchModel.lean" | sha256sum -c -
python3 - "$graph" "$project/DiophantineConsistency" <<'PYTHON'
from pathlib import Path
import sys
graph,project=map(Path,sys.argv[1:]); allowed={'PRAHistoryResultGraph.olean','PRAHistoryTrace.olean','PRAHistoryIterator.olean','PRAHistorySingletonSequence.olean','PRAHistorySingletonMembership.olean','PRAHistoryLengthUnique.olean'}
real={p.name for p in graph.iterdir() if p.is_file() and not p.is_symlink()}
if real != allowed: raise SystemExit(f'unexpected graph real-file set: {real ^ allowed}')
for p in graph.iterdir():
  if p.is_symlink() and not p.resolve().is_relative_to(project.resolve()):
    raise SystemExit(f'graph symlink outside project foundation: {p}')
print('Graph namespace: six pinned real objects; all other objects link to project foundation')
PYTHON
mkdir -p "$out"
cd "$repo"
export PA194_FETCH_PROJECT_FOUNDATION="$project"
export PA194_FETCH_PACKAGE_FOUNDATION="$package"
export PA194_FETCH_GRAPH_NAMESPACE="$graph"
python3 -B "$src/check_fetch_closure_v2.py" --top "$src/PA194SchedulerFetchModel.lean" --reports 2 --out "$out"
