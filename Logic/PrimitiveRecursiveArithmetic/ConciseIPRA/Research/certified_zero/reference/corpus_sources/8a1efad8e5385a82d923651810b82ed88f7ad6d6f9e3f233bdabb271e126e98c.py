"""Optional retrieval of the exact 16 pinned comparison ZIPs.

No downloaded source is executed. The stored Git blob SHA is verified.
Run this only to repeat the full corpus inventory, not to run the checker.
"""
import argparse
import concurrent.futures
import hashlib
import json
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'baselines')
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'evidence' / 'pinned_sources.json').read_text())
    args.output.mkdir(parents=True, exist_ok=True)

    def get(item):
        path = args.output / item['name']
        if path.exists():
            data = path.read_bytes()
        else:
            url = ('https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/'
                   + manifest['head'] + '/' + item['path'])
            with urllib.request.urlopen(url, timeout=120) as response:
                data = response.read()
        digest = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if digest != item['sha']:
            raise ValueError('Pinned Git blob mismatch: ' + item['name'])
        path.write_bytes(data)
        return {'file': item['name'], 'bytes': len(data), 'git_blob': digest}

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        for result in executor.map(get, manifest['files']):
            print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
