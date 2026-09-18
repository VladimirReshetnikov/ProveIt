"""Create an original-archive patch, preserving CRLF in the old scan.py hunks."""
from pathlib import Path
import difflib
ROOT = Path(__file__).resolve().parents[1]
old_root, new_root = ROOT/'baseline/fastunknot', ROOT/'fastunknot'
patch = []
for name in sorted({p.name for p in old_root.glob('*.py')} |
                   {p.name for p in new_root.glob('*.py')}):
    a, b = old_root/name, new_root/name
    old = a.read_bytes().decode('utf-8').splitlines(True) if a.exists() else []
    new = b.read_bytes().decode('utf-8').splitlines(True) if b.exists() else []
    if old != new:
        patch.extend(difflib.unified_diff(
            old, new, fromfile=f'a/fast/fastunknot/{name}' if a.exists() else '/dev/null',
            tofile=f'b/fast/fastunknot/{name}' if b.exists() else '/dev/null'))
(ROOT/'acceleration.patch').write_bytes(''.join(patch).encode('utf-8'))
print('Wrote acceleration.patch')
