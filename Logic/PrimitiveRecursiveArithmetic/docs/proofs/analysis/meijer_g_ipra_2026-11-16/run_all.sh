#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
./run_checks.sh
./build_pdf.sh
