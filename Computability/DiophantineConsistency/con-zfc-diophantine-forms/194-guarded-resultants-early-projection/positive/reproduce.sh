#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B build.py --check
python3 -B verify.py --deep --mutations --receipt CHECK.json
python3 -B -O verify.py --deep --mutations --receipt CHECK_OPTIMIZED.json
cmp CHECK.json CHECK_OPTIMIZED.json
python3 -B parent/build.py --check
p=$(mktemp -d)
trap 'rm -rf "$p"' EXIT HUP INT TERM
python3 -B parent/verify.py --deep --mutations --receipt "$p/parent.json"
python3 -B -O parent/verify.py --deep --mutations --receipt "$p/parent_opt.json"
cmp "$p/parent.json" "$p/parent_opt.json"
cmp "$p/parent.json" parent/CHECK_DEEP.json
