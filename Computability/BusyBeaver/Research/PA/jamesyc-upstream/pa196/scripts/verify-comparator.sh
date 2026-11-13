#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

bwrap --unshare-user --ro-bind / / true
prefix=$(lean --print-prefix)
config=$(mktemp)
trap 'rm -f "$config"' EXIT

# Palomar sets the independent kernels in its protected runtime configuration.
# Mirror that setup locally with the checkers from the pinned Lean toolchain.
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = map(Path, sys.argv[1:])
config = json.loads(source.read_text())
config["external_kernels"] = {
    "nanoda": [str(prefix / "bin/nanoda_bin")],
    "con-ron": [str(prefix / "bin/con-ron")],
}
Path(destination).write_text(json.dumps(config))
PY

lake comparator --config "$config"
