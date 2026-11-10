#!/usr/bin/env python3
"""Optionally retrieve the exact public source corpus for a fresh full audit."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    destination = args.destination.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((ROOT/'evidence/repository_snapshot.json').read_text())
    for entry in manifest['files']:
        url = ('https://raw.githubusercontent.com/' + manifest['repository']
               + '/' + manifest['commit'] + '/' + entry['path'])
        payload = urllib.request.urlopen(url, timeout=60).read()
        actual = hashlib.sha1(b'blob ' + str(len(payload)).encode() + b'\0' + payload).hexdigest()
        if actual != entry['sha']:
            raise RuntimeError('Git blob mismatch: ' + entry['name'])
        archive = destination / entry['name']
        archive.write_bytes(payload)
        target = destination / archive.stem
        target.mkdir(exist_ok=True)
        with zipfile.ZipFile(archive) as z:
            for info in z.infolist():
                p = PurePosixPath(info.filename)
                if p.is_absolute() or '..' in p.parts:
                    raise RuntimeError('Unsafe archive path')
            z.extractall(target)
        print(entry['name'] + ': verified and extracted')

if __name__ == '__main__':
    main()
