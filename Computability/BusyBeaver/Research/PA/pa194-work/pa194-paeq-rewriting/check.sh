#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
printf '%s  %s\n' \
  e0fbd262ad87a27388e474f5a940e3a2f26a3104255a7183573e4f02179821fa Computability/BusyBeaver/Research/PA/pa194-work/pa194-paeq-formula/PA194PAeqSyntax.lean \
  82121fe2c0a90d5d66de452c37e1773769f755f56e42180598c5bed78388c60e "$IPRA_FOUNDATION_OVERLAY/Foundation/FirstOrder/Arithmetic/Basic/Misc.olean" | sha256sum --strict -c
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-paeq-rewriting.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194PAeqSyntax.olean" Computability/BusyBeaver/Research/PA/pa194-work/pa194-paeq-formula/PA194PAeqSyntax.lean | tee "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194PAeqRewriting.olean" Computability/BusyBeaver/Research/PA/pa194-work/pa194-paeq-rewriting/PA194PAeqRewriting.lean | tee -a "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in theorem dependencies' >&2
  exit 1
fi
