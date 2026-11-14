#!/usr/bin/env bash
set -euo pipefail

# Run from the repository root; all generated objects stay on tmpfs.
task_dir=$(mktemp -d /dev/shm/pa195-global-check.XXXXXXXX)
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
base=Computability/BusyBeaver/Research/PA
build() {
  lean -M6000 -j1 -o "$task_dir/$2.olean" "$base/$1/$2.lean"
}
build pa195-quotient PA195LocalQuotient
build pa195-all-tape PA195AllTape
build pa195-translate PA195Translate
build pa195-ordinary PA195Ordinary
build pa195-simulation PA195Simulation
build pa195-generic-trace PA195GenericTrace
build pa195-control PA195ControlData
build pa195-control PA195Control
lean -M6000 -j1 "$base/pa195-global/PA195Global.lean"
