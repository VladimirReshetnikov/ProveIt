#!/usr/bin/env bash
set -euo pipefail
bundle_root="$(cd -- "$(dirname -- "$0")" && pwd)"
python3 "$bundle_root/code/norm_certificates.py"
python3 "$bundle_root/code/adic_norm_validation.py"
python3 "$bundle_root/code/convex_clouds.py"
