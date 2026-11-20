#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
lake build
lake env lean AxiomAudit.lean
lake env lean Examples.lean
