#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
"${PYTHON:-python3}" - <<'PY'
from pathlib import Path
import hashlib
for line in Path('SHA256SUMS').read_text().splitlines():
    expected, filename = line.split('  ', 1)
    path = Path(filename)
    if path.is_absolute() or '..' in path.parts:
        raise SystemExit('Unsafe manifest path')
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f'Manifest mismatch: {filename}')
print('PASS release manifest')
PY
bash code/reproduce.sh "$@"
old_hash="$("${PYTHON:-python3}" -c 'import hashlib; print(hashlib.sha256(open("report.pdf","rb").read()).hexdigest())')"
bash build_pdf.sh
new_hash="$("${PYTHON:-python3}" -c 'import hashlib; print(hashlib.sha256(open("report.pdf","rb").read()).hexdigest())')"
if [[ "$old_hash" == "$new_hash" ]]; then
 printf 'PASS byte-identical PDF rebuild: %s\n' "$new_hash"
else
 printf 'PDF bytes differ from the release (possibly TeX/font versions).\n'
 printf 'Release: %s\nRebuilt: %s\n' "$old_hash" "$new_hash"
 printf 'Compare extracted text and every rendered page before treating this as equivalent.\n'
 exit 2
fi
