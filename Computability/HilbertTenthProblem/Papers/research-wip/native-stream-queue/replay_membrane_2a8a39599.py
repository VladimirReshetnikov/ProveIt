#!/usr/bin/env python3
"""Authenticate both membrane archives, extract private copies, replay the full review.

Default helper, saved receipt and inventory are sibling artifacts. --repo can be
omitted when this script is placed inside a repository. Retired archives are read
from their pinned arrival commit without changing the worktree or Git state.
"""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath, PureWindowsPath
import stat
import subprocess
import sys
import tempfile
import zipfile

if not __debug__:
    raise RuntimeError('This research replay requires Python assertions; omit -O')
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ARRIVAL = '2a8a3959980457aeb0fcf62e26860c809b5a2f42'
RECORDS = (
    ('universal', 'Universal_Membrane_Research_Package.zip', 'literal-membrane-release',
     'dc4fe8f07c278614d567029e40bbdf2db2326e5ea4b04f423bcc3b0b2610e3b5'),
    ('motif', 'Membrane_Motif_Research_Package.zip', 'membrane-motif-release',
     '47da14f271cccfb16fceb5cec859889a02d14e6ff5c23ca121f6f17a1ac98e99'),
)
PINS = {
    'helper': '199bba0d12e3c81006b38c5d17e60b7be9db290ca9f923b799d1298a364c6ccb',
    'receipt': 'a357169fe75be54b124ee8fbe80330032cb07aeaef8ccce08857798fdb5b7764',
    'inventory': '81fccbf99ddd17f4b8937a59b76a75b3bd489b73a68828162211c95fc2d4a09b',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    # Unlike Python equality, distinguishes 1, 1.0 and True everywhere.
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def find_repo():
    for start in (HERE, Path.cwd().resolve()):
        for candidate in (start, *start.parents):
            if (candidate / '.git').exists():
                return candidate
    raise ValueError('Cannot locate repository; supply --repo')


def archive_bytes(repo, name):
    relative = 'docs/incoming/' + name
    path = repo / relative
    if path.is_file():
        return path.read_bytes()
    result = subprocess.run(
        ['git', 'show', ARRIVAL + ':' + relative], cwd=repo,
        capture_output=True, timeout=60,
    )
    require(result.returncode == 0, 'Cannot read archived input: ' + relative)
    return result.stdout


def safe_extract(data, destination):
    """Return a normalized inventory; refuse traversal, duplicate and special files."""
    destination = Path(destination)
    destination.mkdir(parents=True, exist_ok=False)
    inventory = []
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        entries = archive.infolist()
        seen = set()
        checked = []
        for entry in entries:
            name = entry.filename
            path = PurePosixPath(name)
            parts = name.rstrip('/').split('/')
            mode = stat.S_IFMT(entry.external_attr >> 16)
            require(
                bool(name) and '\x00' not in name and '\\' not in name
                and not path.is_absolute() and not PureWindowsPath(name).drive
                and all(part not in ('', '.', '..') for part in parts)
                and mode in (0, stat.S_IFREG, stat.S_IFDIR),
                'Unsafe archive member: ' + repr(name),
            )
            normalized = path.as_posix().rstrip('/')
            require(normalized not in seen, 'Duplicate archive member: ' + name)
            seen.add(normalized)
            checked.append((entry, path))
        # Validate every member before writing any member contents.
        for entry, path in checked:
            target = destination.joinpath(*path.parts)
            require(target.resolve().is_relative_to(destination.resolve()),
                    'Archive member escapes extraction root')
            if entry.is_dir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            content = archive.read(entry)
            require(len(content) == entry.file_size, 'Archive size mismatch')
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open('xb') as handle:
                handle.write(content)
            inventory.append({'path': path.as_posix(), 'size': len(content),
                              'sha256': digest(content)})
    return sorted(inventory, key=lambda member: member['path'])


def run(repo, helper, receipt, inventory):
    repo = Path(repo).resolve()
    paths = {'helper': Path(helper).resolve(), 'receipt': Path(receipt).resolve(),
             'inventory': Path(inventory).resolve()}
    for name, path in paths.items():
        require(digest(path.read_bytes()) == PINS[name], name + ' artifact changed')
    expected = json.loads(paths['receipt'].read_text())
    expected_inventory = json.loads(paths['inventory'].read_text())
    with tempfile.TemporaryDirectory(prefix='membrane-archive-replay-') as temporary:
        temporary = Path(temporary)
        roots = {}
        actual_inventory = []
        for key, name, inner, wanted in RECORDS:
            data = archive_bytes(repo, name)
            require(digest(data) == wanted, 'Archive changed: ' + name)
            destination = temporary / key
            members = safe_extract(data, destination)
            actual_inventory.append({'archive': 'docs/incoming/' + name,
                                     'sha256': wanted, 'members': members})
            roots[key] = destination / inner
            require(roots[key].is_dir(), 'Missing release root: ' + inner)
        actual_inventory.sort(key=lambda entry: entry['archive'])
        require(canonical(actual_inventory) == canonical(expected_inventory),
                'Complete archive member inventory differs')
        fresh = temporary / 'fresh_review.json'
        command = [sys.executable, str(paths['helper']), str(roots['universal']),
                   str(roots['motif']), '--authors', '--output', str(fresh)]
        result = subprocess.run(
            command, text=True, capture_output=True, timeout=900,
            env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0'),
        )
        require(result.returncode == 0,
                'Complete review replay failed:\n' + result.stdout[-4000:] + result.stderr[-4000:])
        actual = json.loads(fresh.read_text())
        require(canonical(actual) == canonical(expected), 'Complete saved review receipt differs')
    return {'status': 'PASS', 'authenticated_archives': len(RECORDS),
            'authenticated_archive_members': sum(len(r['members']) for r in actual_inventory),
            'complete_member_inventory_exact': True,
            'original_author_suite_commands': 18, 'original_loader_checks': 2,
            'complete_review_receipt_exact': True,
            'helper_sha256': PINS['helper'], 'review_receipt_sha256': PINS['receipt'],
            'inventory_sha256': PINS['inventory']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--helper', type=Path, default=HERE / 'review_membrane_reports_2a8a.py')
    parser.add_argument('--receipt', type=Path, default=HERE / 'review_membrane_reports_2a8a.json')
    parser.add_argument('--inventory', type=Path, default=HERE / 'review_membrane_inventory_2a8a.json')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.repo or find_repo(), args.helper, args.receipt, args.inventory)
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
