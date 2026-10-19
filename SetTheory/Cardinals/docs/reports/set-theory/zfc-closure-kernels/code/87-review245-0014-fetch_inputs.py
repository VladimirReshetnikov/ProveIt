"""Retrieve exact pinned input DATA, without executing any downloaded code.

Usage: python3 -B code/fetch_inputs.py [--archive /path/to/source.zip]
The default downloads the pinned archive into memory, validates it, then writes
only the allowlisted members in INPUTS.json. No archive file is redistributed.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import io
import json
import os
import stat
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parent.parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--output', type=Path, default=Path(os.environ.get('B245_INPUTS', ROOT / 'inputs')))
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'INPUTS.json').read_text())
    if args.archive:
        payload = args.archive.read_bytes()
    else:
        req = urllib.request.Request(manifest['archive_url'], headers={'User-Agent': 'ProveIt-245-independent-review/1'})
        with urllib.request.urlopen(req, timeout=120) as response:
            payload = response.read(manifest['archive_bytes'] + 1)
    require(len(payload) == manifest['archive_bytes'], 'Archive size mismatch')
    require(hashlib.sha256(payload).hexdigest() == manifest['archive_sha256'], 'Archive SHA-256 mismatch')
    blob_header = b'blob ' + str(len(payload)).encode() + b'\0'
    require(hashlib.sha1(blob_header + payload).hexdigest() == manifest['archive_git_blob_sha1'], 'Archive Git blob mismatch')
    archive = zipfile.ZipFile(io.BytesIO(payload))
    names = archive.namelist()
    require(len(names) == len(set(names)), 'Duplicate ZIP member names')
    destination_root = args.output.resolve()
    checked = []
    for item in manifest['inputs']:
        member = PurePosixPath(item['archive_member'])
        relative = PurePosixPath(item['destination'])
        require(not member.is_absolute() and '..' not in member.parts, 'Unsafe member name')
        require(not relative.is_absolute() and '..' not in relative.parts, 'Unsafe destination')
        info = archive.getinfo(str(member))
        require(not stat.S_ISLNK(info.external_attr >> 16), 'Symbolic link member rejected')
        require(not info.is_dir() and info.file_size == item['bytes'], 'Input size mismatch')
        content = archive.read(info)
        require(hashlib.sha256(content).hexdigest() == item['sha256'], 'Input hash mismatch: ' + str(relative))
        path = (destination_root / str(relative)).resolve()
        require(path.is_relative_to(destination_root), 'Destination escapes input directory')
        checked.append((path, content))
    # Verify every member before writing any. Inputs remain data only.
    for path, content in checked:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    print(f'Validated and wrote {len(checked)} inert input files to {destination_root}')


if __name__ == '__main__':
    main()
