#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
export PA196_EXTRA_CHECK="$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/check-assembly-in-overlay.sh"
exec bash "$repo/Computability/BusyBeaver/Research/PA/pa196-vs-u208/ipra/check.sh"
