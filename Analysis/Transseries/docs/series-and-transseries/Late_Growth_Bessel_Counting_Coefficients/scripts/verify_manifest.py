"""Verify the release manifest, or only its generated results/PDF entries."""
import hashlib
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parents[1]
mode = sys.argv[1:] or ['--all']
assert mode in [['--all'], ['--results-only'], ['--pdf-only']], 'Unknown verification mode'
count = 0
for line in (root / 'MANIFEST.sha256').read_text().splitlines():
    expected, name = line.split('  ', 1)
    if mode == ['--results-only'] and not name.startswith('results/'):
        continue
    if mode == ['--pdf-only'] and name != 'bessel_late_growth.pdf':
        continue
    path = root / name
    assert path.is_file(), f'Missing file: {name}'
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual == expected, f'SHA-256 mismatch: {name}\nexpected {expected}\nactual   {actual}'
    count += 1
print(f'PASS: {count} manifest entries verified ({mode[0]})')
