#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
export PA196_EXTRA_CHECK="$repo/Computability/BusyBeaver/Research/PA/other-machines/pa195/ipra/check-assembly-in-overlay.sh"
exec bash "$repo/Computability/BusyBeaver/Research/PA/other-machines/pa196-vs-u208/ipra/check.sh"
