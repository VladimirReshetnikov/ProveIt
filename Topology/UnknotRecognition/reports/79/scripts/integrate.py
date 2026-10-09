#!/usr/bin/env python3
"""Preflight the pinned native baseline and add only absent package payloads.

Dry-run is the default.  No project module is imported, and no destination
directory is created until every prerequisite, payload, and destination has
passed the complete preflight.  Existing differing files are never replaced.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import sys


PACKAGE = Path(__file__).resolve().parents[1]
CLASSIFICATIONS = {'native unchanged', 'incoming absent addition', 'new report addition'}


def digest(path):
    hasher = sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            hasher.update(block)
    return hasher.hexdigest()


def relative(value):
    if type(value) is not str or not value or '\\' in value or '\x00' in value:
        raise ValueError('invalid manifest path')
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in ('', '.', '..') for part in value.split('/')):
        raise ValueError('manifest paths must be normalized relative paths')
    return path


def safe_path(root, value):
    parts = relative(value).parts
    current = root
    for index, part in enumerate(parts):
        current = current/part
        if current.is_symlink():
            raise ValueError('symlink in payload or destination path: '+value)
        if current.exists() and index+1 < len(parts) and not current.is_dir():
            raise ValueError('non-directory parent in path: '+value)
    return current


def read_manifest():
    manifest = json.loads((PACKAGE/'integration_manifest.json').read_text())
    if manifest.get('schema') != 'unknot-causal-integration-manifest-v1':
        raise ValueError('unsupported integration manifest schema')
    prerequisite_path = safe_path(PACKAGE, manifest['prerequisite_manifest'])
    prerequisites = json.loads(prerequisite_path.read_text())
    if (prerequisites.get('schema') != 'unknot-native-prerequisites-v1'
            or prerequisites.get('baseline_commit') != manifest.get('baseline_commit')):
        raise ValueError('native prerequisite manifest does not match the baseline')
    entries = manifest['entries']
    if type(entries) is not list or type(prerequisites['entries']) is not list:
        raise ValueError('manifest entries must be lists')
    sources, destinations, native = set(), set(), {}
    for entry in entries:
        source, destination = relative(entry['source']), relative(entry['destination'])
        if source.parts[0] != 'repro' or destination.parts[:2] != ('Topology', 'UnknotRecognition'):
            raise ValueError('integration entry is outside the declared project scope')
        if entry['source'] in sources or entry['destination'] in destinations:
            raise ValueError('duplicate integration entry')
        sources.add(entry['source'])
        destinations.add(entry['destination'])
        if (entry['classification'] not in CLASSIFICATIONS
                or not re.fullmatch('[0-9a-f]{64}', entry['sha256'])
                or type(entry['size_bytes']) is not int or entry['size_bytes'] < 0):
            raise ValueError('malformed integration file record')
        if entry['classification'] == 'native unchanged':
            native[entry['destination']] = (entry['sha256'], entry['size_bytes'])
    recorded = {}
    for entry in prerequisites['entries']:
        relative(entry['path'])
        if entry['path'] in recorded:
            raise ValueError('duplicate native prerequisite')
        recorded[entry['path']] = (entry['sha256'], entry['size_bytes'])
    if native != recorded:
        raise ValueError('native prerequisites do not cover exactly all native payload entries')
    return manifest, prerequisites


def check_file(path, expected_hash, expected_size):
    if not path.is_file():
        return 'missing regular file'
    if path.stat().st_size != expected_size or digest(path) != expected_hash:
        return 'content differs'
    return None


def refusal(stage, errors):
    return dict(status='REFUSED', stage=stage, error_count=len(errors),
                errors=errors[:30], written_files=0)


def integrate(repository, apply=False):
    repo = Path(repository).expanduser().resolve()
    if not repo.is_dir():
        raise ValueError('--repo must name an existing repository directory')
    manifest, prerequisites = read_manifest()
    errors = []
    # Check the entire recorded native baseline before inspecting additions.
    for entry in prerequisites['entries']:
        try:
            path = safe_path(repo, entry['path'])
            problem = check_file(path, entry['sha256'], entry['size_bytes'])
            if problem:
                errors.append(dict(path=entry['path'], reason=problem))
        except (ValueError, OSError) as error:
            errors.append(dict(path=entry['path'], reason=str(error)))
    if errors:
        return refusal('native prerequisites', errors)

    additions = []
    identical = 0
    for entry in manifest['entries']:
        try:
            source = safe_path(PACKAGE, entry['source'])
            problem = check_file(source, entry['sha256'], entry['size_bytes'])
            if problem:
                errors.append(dict(path=entry['source'], reason='package payload '+problem))
                continue
            destination = safe_path(repo, entry['destination'])
            if destination.exists():
                problem = check_file(destination, entry['sha256'], entry['size_bytes'])
                if problem:
                    errors.append(dict(path=entry['destination'], reason=problem))
                else:
                    identical += 1
            else:
                additions.append(entry)
        except (ValueError, OSError) as error:
            errors.append(dict(path=entry['destination'], reason=str(error)))
    if errors:
        return refusal('payload and destination preflight', errors)

    written = 0
    if apply:
        for entry in additions:
            source = safe_path(PACKAGE, entry['source'])
            destination = safe_path(repo, entry['destination'])
            payload = source.read_bytes()
            if len(payload) != entry['size_bytes'] or sha256(payload).hexdigest() != entry['sha256']:
                raise ValueError('package payload changed after preflight: '+entry['source'])
            # Exclusive creation protects against replacing a file introduced
            # after preflight.  Use a quiescent destination during integration.
            destination.parent.mkdir(parents=True, exist_ok=True)
            with destination.open('xb') as outgoing:
                outgoing.write(payload)
            shutil.copystat(source, destination, follow_symlinks=False)
            written += 1
    return dict(status='APPLIED' if apply else 'DRY_RUN', repository=str(repo),
        baseline_commit=manifest['baseline_commit'],
        checked_native_prerequisites=len(prerequisites['entries']),
        checked_payload_files=len(manifest['entries']), identical_files=identical,
        planned_additions=len(additions), written_files=written,
        additions=[entry['destination'] for entry in additions])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True)
    parser.add_argument('--apply', action='store_true', help='add absent files after full preflight')
    arguments = parser.parse_args()
    try:
        result = integrate(arguments.repo, apply=arguments.apply)
        print(json.dumps(result, indent=2))
        return 2 if result['status'] == 'REFUSED' else 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps(dict(status='ERROR', reason=str(error)), indent=2))
        return 2


if __name__ == '__main__':
    sys.exit(main())
