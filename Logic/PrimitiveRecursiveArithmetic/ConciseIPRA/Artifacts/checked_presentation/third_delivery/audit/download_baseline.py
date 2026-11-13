"""Download exact public source bytes named by a pinned census manifest.

Alternatively use an existing ProveIt checkout containing the manifest's
paths. No download is necessary when replaying from such a checkout.
"""
import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import urllib.parse
import urllib.request


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--destination', type=Path, required=True)
    p.add_argument('--workers', type=int, default=8)
    args = p.parse_args()
    manifest = json.loads(args.manifest.read_text())
    revision = manifest['revision']
    repository = manifest['repository'].removeprefix('https://github.com/')
    base = 'https://raw.githubusercontent.com/' + repository + '/' + revision + '/'

    def fetch(record):
        relative = Path(record['path'])
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError('Unsafe manifest path')
        target = args.destination / relative
        if target.is_file():
            data = target.read_bytes()
            if hashlib.sha256(data).hexdigest() == record['sha256']:
                return 'retained'
        url = base + urllib.parse.quote(record['path'], safe='/')
        data = urllib.request.urlopen(url, timeout=60).read()
        if len(data) != record['bytes'] or hashlib.sha256(data).hexdigest() != record['sha256']:
            raise ValueError('Source identity mismatch: ' + record['path'])
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        return 'downloaded'

    counts = {'retained': 0, 'downloaded': 0}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        for result in pool.map(fetch, manifest['files']):
            counts[result] += 1
    print(json.dumps({'revision': revision, 'files': counts,
                      'destination': str(args.destination.resolve())}, indent=2))


if __name__ == '__main__':
    main()
