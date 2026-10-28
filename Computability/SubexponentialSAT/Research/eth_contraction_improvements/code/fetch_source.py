#!/usr/bin/env python3
"""Fetch the four pinned upstream source files and verify their Git blob hashes.

This optional reproducibility helper requires internet access. It does not
execute the downloaded sources or change any remote repository.
"""

import argparse
import hashlib
import json
from pathlib import Path
import urllib.request


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', default='upstream_source')
    args = parser.parse_args()
    package = Path(__file__).resolve().parents[1]
    manifest = json.loads((package / 'source_manifest.json').read_text())
    destination = Path(args.destination)
    destination.mkdir(parents=True, exist_ok=True)
    for item in manifest['files']:
        url = ('https://raw.githubusercontent.com/openai/math/'
               + manifest['commit'] + '/' + item['path'])
        request = urllib.request.Request(url, headers={'User-Agent': 'exact-counting-research-note/1.0'})
        with urllib.request.urlopen(request, timeout=60) as response:
            data = response.read()
        git_header = b'blob ' + str(len(data)).encode('ascii') + b'\0'
        actual = hashlib.sha1(git_header + data).hexdigest()
        if actual != item['git_blob_sha']:
            raise RuntimeError('Git blob mismatch for ' + item['file'])
        if hashlib.sha256(data).hexdigest() != item['sha256_local']:
            raise RuntimeError('SHA-256 mismatch for ' + item['file'])
        target = destination / item['file']
        if target.exists() and target.read_bytes() != data:
            raise FileExistsError('Refusing to replace different bytes: ' + str(target))
        target.write_bytes(data)
        print('Verified:', target)


if __name__ == '__main__':
    main()
