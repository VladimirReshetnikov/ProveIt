#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"
python code/verify_exact.py --max-q 60
python code/verify_characters.py --max-q 60
python code/verify_s4_presentation.py
python code/replay_certificate.py
python code/verify_numeric.py --group traces --dps 55
python code/verify_numeric.py --group stieltjes --dps 55
python code/verify_numeric.py --group s4 --dps 55
echo 'All exact and numerical regression groups passed.'
