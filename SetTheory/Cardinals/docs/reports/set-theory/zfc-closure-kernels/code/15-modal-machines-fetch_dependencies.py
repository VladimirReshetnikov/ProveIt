#!/usr/bin/env python3
"""Fetch only the nine pinned public files needed to replay the candidates."""
import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import urllib.request

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', type=Path, default=HERE / 'upstream')
    args = parser.parse_args()
    pins = json.loads((HERE / 'source_pins.json').read_text())
    destination = args.destination.resolve()
    base = f"https://raw.githubusercontent.com/{pins['repository']}/{pins['commit']}/"
    def fetch(item):
        relative, digest = item
        path = destination / relative
        if path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == digest:
            return relative
        request = urllib.request.Request(base + relative, headers={'User-Agent': 'ZFC-grammar-reproducer'})
        with urllib.request.urlopen(request, timeout=45) as response:
            data = response.read()
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError('Downloaded source hash mismatch: ' + relative)
        if path.exists():
            raise FileExistsError('Refusing to replace different local content: ' + str(path))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return relative
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        files = list(pool.map(fetch, pins['files'].items()))
    print(f'Fetched and checked {len(files)} pinned files in {destination}')
    print('Now run verify_candidates.py --repo ' + str(destination))


if __name__ == '__main__': main()
