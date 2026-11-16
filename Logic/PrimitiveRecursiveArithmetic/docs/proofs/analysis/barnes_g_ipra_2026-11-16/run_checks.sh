#!/usr/bin/env sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
python3 "$ROOT/code/verify_finite_core.py" --limit 24 --output "$ROOT/evidence/finite_core.json"
python3 "$ROOT/code/check_numeric_identities.py" --dps 90 --output "$ROOT/evidence/numeric_validation.json"
python3 "$ROOT/code/certified_product.py" --output "$ROOT/evidence/product_certificates.json"
python3 "$ROOT/code/audit_scaffold.py" --root "$ROOT" --output "$ROOT/evidence/scaffold_audit.json"
