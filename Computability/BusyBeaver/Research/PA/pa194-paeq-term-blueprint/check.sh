#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA/pa194-paeq-term-blueprint
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-paeq-term-blueprint.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
sha256sum -c "$base/upstream.sha256"
export LEAN_PATH="$root:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/PA194PAeqTermBlueprint.olean" "$base/PA194PAeqTermBlueprint.lean" | tee "$root/axioms.log"
lean -M6000 -j1 -o "$root/PA194PAeqTermCode.olean" "$base/PA194PAeqTermCode.lean" | tee -a "$root/axioms.log"
if rg -q 'sorryAx' "$root/axioms.log"; then exit 1; fi
