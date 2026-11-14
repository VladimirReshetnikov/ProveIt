#!/usr/bin/env bash
set -euo pipefail

# Run from the repository root; all generated objects stay on tmpfs.
task_dir=$(mktemp -d /dev/shm/pa194-dense-check.XXXXXXXX)
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
base=Computability/BusyBeaver/Research/PA
build() {
  lean -M6000 -j1 -o "$task_dir/$2.olean" "$base/$1/$2.lean"
}
build pa194-quotient PA194LocalQuotient
build pa194-all-tape PA194AllTape
build pa194-translate PA194Translate
build pa194-ordinary PA194Ordinary
build pa194-simulation PA194Simulation
build pa195-generic-trace PA195GenericTrace
build pa194-control PA194ControlData
build pa194-control PA194Control
build pa194-global PA194Global
build pa194-dense PA194DenseData
build pa194-dense PA194DenseBinding
lean -M6000 -j1 "$base/pa194-dense/PA194DenseGlobal.lean"
