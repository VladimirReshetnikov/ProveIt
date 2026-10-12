#!/usr/bin/env python3
"""Check this source overlay, apply it explicitly, or verify installed bytes.

Requires Python 3.10+ and Git; uses only the Python standard library.
No files are changed unless --apply is supplied. No staging or commits occur.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys


HERE = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def relative_path(value):
    path = PurePosixPath(value)
    if path.is_absolute() or not path.parts or '..' in path.parts:
        raise ValueError('unsafe repository-relative path in manifest')
    return Path(*path.parts)


def git(repo, *args):
    result = subprocess.run(['git', '-c', 'core.autocrlf=false', *args],
                            cwd=repo, text=True, capture_output=True)
    if result.returncode:
        raise ValueError((result.stderr or result.stdout).strip() or 'Git command failed')
    return result.stdout.strip()


def verify_bundle(manifest):
    if manifest.get('format') != 'proveit-unknot-integration-v1':
        raise ValueError('unsupported manifest format')
    if len(manifest['files']) != manifest['file_count']:
        raise ValueError('manifest file count does not match its entries')
    seen = set()
    for record in manifest['files']:
        path = relative_path(record['path'])
        if path in seen:
            raise ValueError('duplicate repository path in manifest')
        seen.add(path)
        full = HERE / relative_path(record['full_file'])
        if not full.is_file() or digest(full) != record['new_sha256']:
            raise ValueError('full-file hash mismatch: ' + record['path'])
    patch = HERE / relative_path(manifest['patch']['path'])
    if not patch.is_file() or digest(patch) != manifest['patch']['sha256']:
        raise ValueError('integration.patch hash mismatch')
    return patch


def verify_assets(repo, manifest):
    for asset in manifest.get('required_base_assets', []):
        path = repo / relative_path(asset['path'])
        if not path.is_file() or digest(path) != asset['sha256']:
            raise ValueError('required pinned fixture is missing or changed: ' + asset['path'])


def verify_installed(repo, manifest):
    for record in manifest['files']:
        path = repo / relative_path(record['path'])
        if not path.is_file() or digest(path) != record['new_sha256']:
            raise ValueError('installed hash mismatch: ' + record['path'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, help='root of the target ProveIt checkout')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--apply', action='store_true', help='apply after all preflight checks pass')
    mode.add_argument('--verify-installed', action='store_true', help='check all resulting file hashes')
    mode.add_argument('--verify-bundle', action='store_true', help='check package files only; no Git required')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text(encoding='utf-8'))
    patch = verify_bundle(manifest)
    if args.verify_bundle:
        print('Bundle verified:', manifest['file_count'], 'full files and the patch.')
        return
    if args.repo is None:
        parser.error('--repo is required unless --verify-bundle is used')
    repo = args.repo.resolve()
    verify_assets(repo, manifest)
    if args.verify_installed:
        verify_installed(repo, manifest)
        print('Installed bytes verified for all', manifest['file_count'], 'files.')
        return
    head = git(repo, 'rev-parse', 'HEAD')
    if head != manifest['base_commit']:
        raise ValueError('use a clean worktree at the pinned base ' + manifest['base_commit'])
    for record in manifest['files']:
        path = repo / relative_path(record['path'])
        expected = record['old_sha256']
        if expected is None:
            if path.exists():
                raise ValueError('an added destination already exists: ' + record['path'])
        elif not path.is_file() or digest(path) != expected:
            raise ValueError('baseline bytes differ: ' + record['path'] +
                             '; use an unchanged checkout with LF line endings')
    git(repo, 'apply', '--check', '--', str(patch))
    if not args.apply:
        print('Preflight passed at', head + '; no files were changed.')
        return
    git(repo, 'apply', '--', str(patch))
    verify_installed(repo, manifest)
    print('Applied and verified', manifest['file_count'], 'files; nothing staged or committed.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print('ERROR:', error, file=sys.stderr)
        sys.exit(1)
