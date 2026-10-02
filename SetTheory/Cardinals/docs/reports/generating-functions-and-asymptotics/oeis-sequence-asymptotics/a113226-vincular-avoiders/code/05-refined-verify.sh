#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python verify_package.py "$@"
