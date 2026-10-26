#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B build.py --check
python3 -B verify.py --receipt CHECK.json
python3 -B -O verify.py --receipt CHECK_OPTIMIZED.json
cmp CHECK.json CHECK_OPTIMIZED.json
python3 -B one_anchor7309/build.py --check
python3 -B one_anchor7309/verify.py --receipt one_anchor7309/CHECK.json
python3 -B -O one_anchor7309/verify.py --receipt one_anchor7309/CHECK_OPTIMIZED.json
cmp one_anchor7309/CHECK.json one_anchor7309/CHECK_OPTIMIZED.json
python3 -B q4_interpolation/build.py --check
python3 -B q4_interpolation/verify.py --receipt q4_interpolation/CHECK.json
python3 -B -O q4_interpolation/verify.py --receipt q4_interpolation/CHECK_OPTIMIZED.json
cmp q4_interpolation/CHECK.json q4_interpolation/CHECK_OPTIMIZED.json
