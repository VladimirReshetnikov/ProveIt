#!/usr/bin/env bash
set -euo pipefail
# Fresh checked build, from the repository root, using an isolated tmpfs overlay.
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-ax-core
upstream=$base/jamesyc-upstream/pa196
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-ax-core.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for mod in M6.Source.Syntax M6.Source.PathTrie M6.FastResolve M6.TreeSite; do
  rel=${mod//./\/}
  mkdir -p "$task_dir/$(dirname "$rel")"
  lean -M6000 -j1 -o "$task_dir/$rel.olean" "$upstream/$rel.lean"
done
python3 "$base/pa194-source-tree/generate.py" "$task_dir/PA194SourceTree.lean"
lean -M6000 -j1 --root="$task_dir" -o "$task_dir/PA194SourceTree.olean" "$task_dir/PA194SourceTree.lean"
lean -M6000 -j1 -o "$task_dir/PA194SourceProgram.olean" "$base/pa194-coverage/PA194SourceProgram.lean"
lean -M6000 -j1 -o "$task_dir/PA194AXSource.olean" "$base/pa194-ax-source/PA194AXSource.lean"
while IFS= read -r mod; do
  rel=${mod//./\/}
  mkdir -p "$task_dir/$(dirname "$rel")"
  lean -M6000 -j1 -o "$task_dir/$rel.olean" "$upstream/$rel.lean"
done < "$package/dependencies.txt"
lean -M6000 -j1 -o "$task_dir/PA194AXSymbolic.olean" "$package/PA194AXSymbolic.lean"
python3 "$package/generate.py" "$task_dir"
for file in "$task_dir"/PA194AXBatch*.lean; do
  echo "Checking ${file##*/}"
  lean -M6000 -j1 --root="$task_dir" -o "${file%.lean}.olean" "$file"
done
lean -M6000 -j1 --root="$task_dir" "$task_dir/PA194AXPlan.lean" | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in AX source theorem' >&2
  exit 1
fi
