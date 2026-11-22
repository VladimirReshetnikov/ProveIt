#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 code/check_sparse.py
python3 code/check_graph.py
python3 code/roots_example.py
python3 code/compact_example.py
