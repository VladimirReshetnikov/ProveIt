#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

mkdir -p validation
python3 verify.py 2>&1 | tee validation/python_validation.txt
bash paper/build.sh
python3 make_manifest.py
sha256sum -c MANIFEST.sha256
