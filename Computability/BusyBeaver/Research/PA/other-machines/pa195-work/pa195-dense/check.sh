#!/usr/bin/env bash
set -euo pipefail

# Run from the repository root; all generated objects stay on tmpfs.
task_dir=$(mktemp -d /dev/shm/pa195-dense-check.XXXXXXXX)
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
base=Computability/BusyBeaver/Research/PA
build() {
  lean -M6000 -j1 -o "$task_dir/$2.olean" "$base/$1/$2.lean"
}
build other-machines/pa195-work/pa195-quotient PA195LocalQuotient
build other-machines/pa195-work/pa195-all-tape PA195AllTape
build other-machines/pa195-work/pa195-translate PA195Translate
build other-machines/pa195-work/pa195-ordinary PA195Ordinary
build other-machines/pa195-work/pa195-simulation PA195Simulation
build other-machines/pa195-work/pa195-generic-trace PA195GenericTrace
build other-machines/pa195-work/pa195-control PA195ControlData
build other-machines/pa195-work/pa195-control PA195Control
build other-machines/pa195-work/pa195-global PA195Global
build other-machines/pa195-work/pa195-dense PA195DenseData
build other-machines/pa195-work/pa195-dense PA195DenseBinding
lean -M6000 -j1 "$base/other-machines/pa195-work/pa195-dense/PA195DenseGlobal.lean"
