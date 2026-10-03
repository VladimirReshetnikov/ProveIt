#!/bin/sh
set -eu
cd "$(dirname "$0")"
exec python3 replay/run_release.py "$@"
