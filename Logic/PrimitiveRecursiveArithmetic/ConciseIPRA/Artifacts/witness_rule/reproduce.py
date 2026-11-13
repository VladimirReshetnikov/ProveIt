"""Check package identities, remeasure kernels, and replay focused evidence."""
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

import measure

ROOT = Path(__file__).resolve().parent


def main():
    manifest = ROOT / 'MANIFEST.json'
    if manifest.exists():
        for row in json.loads(manifest.read_text())['files']:
            data = (ROOT / row['path']).read_bytes()
            if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
                raise ValueError('Changed package file: ' + row['path'])
    current = measure.measure()
    saved = json.loads((ROOT / 'evidence/measurements.json').read_text())
    if (current['python'], current['zlib']) == (saved['python'], saved['zlib']):
        if current != saved:
            raise ValueError('Source measurements differ from the delivered record')
    else:
        print('Different Python/zlib version: reporting current measurements without asserting byte equality.')
    for row in current['programs']:
        if row.get('path', '').startswith('code/checker'):
            print(json.dumps(row))
    for relative in ['tests/verify_witness.py', 'tests/verify_choice.py']:
        subprocess.run([sys.executable, str(ROOT / relative)], check=True, cwd=ROOT)
    # The supplementary validator writes examples and receipts. Run a
    # temporary copy so reproduction never alters the delivered package.
    import shutil
    with tempfile.TemporaryDirectory(prefix='ipra-congruence-') as temp:
        work = Path(temp)
        shutil.copyfile(ROOT / 'tests/validate_zero_seed.py', work / 'validate_zero_seed.py')
        shutil.copytree(ROOT / 'tests/reference', work / 'reference')
        subprocess.run([sys.executable, str(work / 'validate_zero_seed.py')], check=True, cwd=work)
    print('All reproduction checks passed.')


if __name__ == '__main__':
    main()
