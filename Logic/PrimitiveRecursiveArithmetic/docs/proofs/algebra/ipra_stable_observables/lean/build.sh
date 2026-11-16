#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake exe cache get Mathlib.Data.Fin.Tuple.Basic
lake build ObjectObservation SpectralBlueprint
lake env lean ObjectAudit.lean
lake env lean SpectralAudit.lean
