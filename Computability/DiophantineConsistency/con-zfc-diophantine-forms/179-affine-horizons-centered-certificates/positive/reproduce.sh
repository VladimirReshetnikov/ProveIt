#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B build.py --check
python3 -B verify.py --receipt CHECK.json
python3 -B -O verify.py --receipt CHECK_OPTIMIZED.json
cmp CHECK.json CHECK_OPTIMIZED.json
python3 -B start_marker4177/build.py --check
python3 -B start_marker4177/verify.py --receipt start_marker4177/CHECK.json
python3 -B -O start_marker4177/verify.py --receipt start_marker4177/CHECK_OPTIMIZED.json
cmp start_marker4177/CHECK.json start_marker4177/CHECK_OPTIMIZED.json
python3 -B build_variants.py --check
python3 -B verify_variants.py --receipt VARIANTS_CHECK.json
python3 -B -O verify_variants.py --receipt VARIANTS_CHECK_OPTIMIZED.json
cmp VARIANTS_CHECK.json VARIANTS_CHECK_OPTIMIZED.json
python3 -B late172/build.py --check
python3 -B late172/verify.py --deep --mutations --receipt late172/CHECK.json
python3 -B -O late172/verify.py --deep --mutations --receipt late172/CHECK_OPTIMIZED.json
cmp late172/CHECK.json late172/CHECK_OPTIMIZED.json
python3 -B late172/parent/build.py --check
parent_tmp=$(mktemp -d)
trap 'rm -rf "$parent_tmp"' EXIT HUP INT TERM
python3 -B late172/parent/verify.py --deep --mutations --receipt "$parent_tmp/PARENT_NORMAL.json"
python3 -B -O late172/parent/verify.py --deep --mutations --receipt "$parent_tmp/PARENT_OPTIMIZED.json"
cmp "$parent_tmp/PARENT_NORMAL.json" "$parent_tmp/PARENT_OPTIMIZED.json"
cmp "$parent_tmp/PARENT_NORMAL.json" late172/parent/CHECK_DEEP.json
