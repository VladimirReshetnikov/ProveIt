#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 verify_manifest.py
work="${RADIX_REPLAY_DIR:-$PWD/replay-output}"
if [[ -e "$work" ]]; then
  printf 'Replay destination already exists; choose an empty path with RADIX_REPLAY_DIR.\n' >&2
  exit 1
fi
mkdir -p "$work/checks"
cp checks/*.py "$work/checks/"
python3 - <<'PY'
import platform,mpmath,sympy
print('Python',platform.python_version(),'mpmath',mpmath.__version__,'SymPy',sympy.__version__)
PY
for task in exact radix coefficients inverse reciprocity; do
  python3 "$work/checks/check_${task}.py" > "$work/${task}.log"
done
python3 checks/verify_results.py recorded "$work/checks" | tee "$work/verification.log"
python3 checks/make_tables.py --data "$work/checks" --output "$work/numerical_tables.tex"
cmp numerical_tables.tex "$work/numerical_tables.tex"
# Use a clean TeX staging directory, without any prebuilt format/font caches.
mkdir -p "$work/article"
cp radix_partition_report.tex numerical_tables.tex build_pdf.sh "$work/article/"
bash "$work/article/build_pdf.sh" | tee "$work/pdf-build.log"
python3 - "$work/article/radix_partition_report.pdf" <<'PY'
from pathlib import Path
import hashlib,sys
p=Path(sys.argv[1]);assert p.read_bytes().startswith(b'%PDF-')
print('Rebuilt PDF SHA256:',hashlib.sha256(p.read_bytes()).hexdigest())
q=Path('radix_partition_report.pdf')
print('Byte-identical to supplied PDF:',p.read_bytes()==q.read_bytes())
PY
printf 'PASS: clean computation replay and TeX build completed\n'
