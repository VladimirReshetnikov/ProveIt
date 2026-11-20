#!/usr/bin/env bash
# Run the Mathlib-dependent and object-language modules from a ProveIt checkout.
set -eu
packet="$(cd "$(dirname "$0")" && pwd)"
checkout="$(cd "${1:?Supply the path to the pinned ProveIt checkout}" && pwd)"
cd "$checkout"
lake build +ConciseIPRA.PR +Mathlib.Algebra.Group.ForwardDiff
lake env bash -eu -c '
    packet=$1
    cache_dir=$(mktemp -d)
    trap '\''rm -rf "$cache_dir"'\'' EXIT
    export LEAN_PATH="$cache_dir${LEAN_PATH:+:$LEAN_PATH}"
    cd "$packet/lean"
    for module in IntervalLift CellGeometry Root; do
        lean -o "$cache_dir/$module.olean" "$module.lean"
        echo "Checked $module"
    done
    cd "$packet/object"
    lean ObjectReplay.lean
' _ "$packet"
