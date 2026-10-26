#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 1 || $# -gt 2 ]]; then
  printf '%s\n' 'Usage: replay.sh /absolute/path/to/ProveIt [--check|--apply]' >&2
  exit 2
fi
MODE="${2:---check}"
if [[ "$MODE" != "--check" && "$MODE" != "--apply" ]]; then
  printf '%s\n' 'Mode must be --check or --apply.' >&2
  exit 2
fi
BUNDLE_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_DIR="$(cd -- "$1" && pwd)"
EXPECTED_COMMIT='7fa06d530df54d4aeb2e18027409df082234c69e'
ACTUAL_COMMIT="$(git -C "$REPO_DIR" rev-parse HEAD)"
if [[ "$ACTUAL_COMMIT" != "$EXPECTED_COMMIT" ]]; then
  printf 'Expected commit %s, found %s\n' "$EXPECTED_COMMIT" "$ACTUAL_COMMIT" >&2
  exit 1
fi
if [[ -n "$(git -C "$REPO_DIR" status --porcelain --untracked-files=no)" ]]; then
  printf '%s\n' 'Tracked source changes are present; use a clean review checkout.' >&2
  exit 1
fi
git -C "$REPO_DIR" apply --check "$BUNDLE_DIR/patches/main.patch"
cd -- "$REPO_DIR"
lake build DiophantineConsistency.QuadraticTreeCodeGraphs DiophantineConsistency.QuadraticBoolean
lake env lean "$BUNDLE_DIR/checks/baseline/PairingClients.lean"
lake env lean "$BUNDLE_DIR/checks/baseline/BooleanClients.lean"
if [[ "$MODE" == "--check" ]]; then
  printf '%s\n' 'Patch dry run and nine baseline constructor equalities passed.'
  printf '%s\n' 'Use --apply on a clean review checkout to apply and build the changes.'
  exit 0
fi
git apply "$BUNDLE_DIR/patches/main.patch"
lake build DiophantineConsistency.MarginFinalizer DiophantineConsistency.NativePellBootstrap \
  DiophantineConsistency.QuadraticTreeCodeGraphs DiophantineConsistency.QuadraticBoolean
lake env lean "$BUNDLE_DIR/checks/IntegratedAxiomAudit.lean"
printf '%s\n' 'Main patch applied; revised module build and integrated axiom audit completed.'
