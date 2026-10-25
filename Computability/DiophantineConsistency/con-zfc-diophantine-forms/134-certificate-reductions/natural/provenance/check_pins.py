#!/usr/bin/env python3
"""Verify the bounded source ledger; optionally authenticate paths against Git."""
from argparse import ArgumentParser
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reverse_edits(data, edits):
    lines = data.decode('utf-8').splitlines(keepends=True)
    starts = [e['after_start'] for e in edits]
    require(starts == sorted(starts), 'Unordered edit sequence')
    for edit in reversed(edits):
        start = edit['after_start']
        end = start + len(edit['after'])
        require(lines[start:end] == edit['after'], 'Edit does not match current bytes')
        lines[start:end] = edit['before']
    return ''.join(lines).encode('utf-8')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path,
                        help='optional ProveIt Git checkout containing the pinned commit')
    args = parser.parse_args()
    pins = json.loads((ROOT / 'SOURCE_PINS.json').read_text())
    engine_bytes = (ROOT / 'ENGINE_MAP.json').read_bytes()
    require(digest(engine_bytes) == pins['engine_map_sha256'], 'ENGINE_MAP hash')
    engine = {e['path']: e for e in json.loads(engine_bytes)}
    require(len(engine) == len(pins['files']) == pins['summary']['engine_files'], 'Engine count')
    require(set(engine) == {e['local_engine_path'] for e in pins['files']}, 'Engine file list')
    inputs_changed = 0
    exports_changed = 0
    for entry in pins['files']:
        original = engine[entry['local_engine_path']]
        local = (ROOT / entry['local_engine_path']).read_bytes()
        require(entry['repository_commit'] == pins['commit'], 'Entry commit')
        require(entry['input_relative_path'] == original['input_relative_path'], 'Input path')
        require(entry['engine_map_path_relocated'] == original['path_relocated'], 'Relocation flag')
        require(digest(local) == original['sha256'] == entry['local_sha256'], 'Final file hash')
        source = reverse_edits(local, entry['input_to_local_edits'])
        require(digest(source) == original['input_sha256'] == entry['input_sha256'], 'Input hash')
        upstream = reverse_edits(source, entry['upstream_to_input_edits'])
        require(digest(upstream) == entry['upstream_sha256']
                == entry['parent_archive_entry']['sha256'], 'Upstream SHA256')
        require(blob(upstream) == entry['repository_git_blob_sha1'], 'Upstream Git blob')
        require([len(upstream), len(source), len(local)]
                == [entry['upstream_bytes'], entry['input_bytes'], entry['local_bytes']], 'Byte counts')
        changed = upstream != source
        require(entry['input_origin'] == ('locally_modified_upstream' if changed
                                          else 'pinned_upstream_bytes'), 'Origin classification')
        inputs_changed += changed
        exports_changed += source != local
    for entry in pins['parent_artifacts']:
        data = (ROOT / entry['local_path']).read_bytes()
        require(digest(data) == entry['sha256'], 'Parent artifact SHA256')
        require(blob(data) == entry['repository_git_blob_sha1'], 'Parent artifact Git blob')
        require(len(data) == entry['bytes'], 'Parent artifact byte count')
    require(inputs_changed == pins['summary']['mathematically_modified_inputs'], 'Modified count')
    require(exports_changed == pins['summary']['files_with_export_edits'], 'Export edit count')
    require(len(engine) - inputs_changed == pins['summary']['input_matches_pinned_upstream'], 'Exact count')
    require(len(pins['parent_artifacts']) == pins['summary']['copied_parent_artifacts'], 'Parent count')
    for size in (233, 234):
        summary = json.loads((ROOT / f'provenance/parent{size}_summary.json').read_text())
        require(summary['natural'] == pins['parent129_comparison'][f'natural{size}'], 'Parent comparison')
    if args.repo:
        raw = subprocess.check_output(['git', '-C', str(args.repo), 'ls-tree', '-r', '-z', pins['commit']])
        tree = {}
        for item in raw.split(b'\0'):
            if item:
                descriptor, path = item.split(b'\t', 1)
                tree[path.decode()] = descriptor.decode().split()[2]
        for entry in pins['files'] + pins['parent_artifacts']:
            require(tree.get(entry['repository_path']) == entry['repository_git_blob_sha1'],
                    'Path/blob binding in pinned Git tree: ' + entry['repository_path'])
        for entry in pins['source_authorities']:
            require(tree.get(entry['repository_path']) == entry['git_blob_sha1'], 'Authority Git tree binding')
    print(json.dumps({'status': 'PASS', **pins['summary'],
                      'pinned_git_tree_checked': bool(args.repo)}))


if __name__ == '__main__':
    main()
