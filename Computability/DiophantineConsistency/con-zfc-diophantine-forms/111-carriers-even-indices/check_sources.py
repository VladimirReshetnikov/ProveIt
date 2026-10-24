#!/usr/bin/env python3
"""Authenticate inherited bytes and archive members; do not reprove semantics."""
from contextlib import ExitStack
from hashlib import sha1, sha256
import json
from pathlib import Path
import subprocess
import sys
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parent


def main():
    ledger = json.loads((ROOT / 'SOURCE_LEDGER.json').read_text())
    archive_members = 0
    git_objects = 0
    with ExitStack() as stack:
        archives = {}
        for entry in ledger['inherited_files']:
            name = entry['local_path']
            data = (ROOT / name).read_bytes()
            if len(data) != entry['bytes'] or sha256(data).hexdigest() != entry['sha256']:
                raise ValueError('Inherited source byte mismatch: ' + name)
            if 'git_blob_sha1' in entry:
                blob = sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
                if blob != entry['git_blob_sha1']:
                    raise ValueError('Inherited Git object mismatch: ' + name)
                git_objects += 1
            if 'local_archive' in entry:
                path = entry['local_archive']
                if path not in archives:
                    archives[path] = stack.enter_context(ZipFile(ROOT / path))
                if archives[path].read(entry['archive_member']) != data:
                    raise ValueError('Included archive member mismatch: ' + name)
                archive_members += 1
    args = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
    result = subprocess.run(args + ['inherited/native/check_provenance.py'],
                            cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    native = json.loads(result.stdout)
    if native.get('status') != 'PASS':
        raise ValueError('Native source provenance checker did not pass')
    print(json.dumps({'status': 'PASS',
                      'inherited_files': len(ledger['inherited_files']),
                      'git_objects': git_objects,
                      'included_archive_members': archive_members,
                      'native_provenance_files': native['files'],
                      'scope': 'Inherited file identities and archive binding only; '
                               'no proof-assistant compilation or reproof of '
                               'unbounded calibration.'}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
