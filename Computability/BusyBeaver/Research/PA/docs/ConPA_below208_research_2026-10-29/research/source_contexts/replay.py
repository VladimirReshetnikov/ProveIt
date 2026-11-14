#!/usr/bin/env python3
"""Portable entry point for the archived source-context experiments.

Default check is finite and fast. Harvest actions rederive all indicated
universal contracts and may take several minutes. Aliases/folds are bounded
discovery screens, not new correctness proofs or state-complexity bounds.
All original experiment code runs in an isolated temporary staging tree.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def check():
    manifest = json.loads((HERE / 'DEPENDENCIES.json').read_text())
    need(manifest['format'] == 1, 'Unknown dependency format')
    for relative, entry in manifest['files'].items():
        path = Path(relative)
        need(not path.is_absolute() and '..' not in path.parts, 'Unsafe dependency path')
        raw = (HERE / path).read_bytes()
        need(digest(raw) == entry['sha256'], 'Dependency hash mismatch: ' + relative)
        decoded = gzip.decompress(raw) if entry['gzip'] else raw
        need(digest(decoded) == entry['uncompressed_sha256'], 'Uncompressed hash mismatch')
    archive = ROOT / manifest['source_archive']['delivery_relative_path']
    need(digest(archive.read_bytes()) == manifest['source_archive']['sha256'], 'Upstream archive hash mismatch')
    for stem, pairs, mutations in [('source_alias208_r4', 42642, 42642),
                                    ('source_fold208_r4', 448, 370944),
                                    ('source_alias208_r4_h10', 42642, 42642),
                                    ('source_fold208_r4_h10', 448, 370944),
                                    ('restricted_alias208_r4_h12', 42849, 42849)]:
        receipt = json.loads((HERE / 'receipts' / (stem + '.json')).read_text())
        need(receipt['pairs'] == pairs and receipt['mutations'] == mutations,
             'Recorded search census mismatch')
        need(receipt['results'] == [], 'Recorded search result differs')
    for name, contracts, steps, rows, windows in [
            ('source_contexts208_r4', 5084, 1251865, 416, 21358),
            ('restricted_contexts208_r4', 5079, 1243924, 416, 12490)]:
        data = json.loads((HERE / 'data' / (name + '.json')).read_text())
        runtime = data['runtime']
        need(runtime['contracts'] == contracts and runtime['symbolic_inferences'] == steps,
             'Recorded contract census mismatch')
        need(runtime['literal_rows_covered'] == rows and data['window_count'] == windows,
             'Recorded row/window census mismatch')
        need(sum(len(v) for v in data['windows'].values()) == windows, 'Window data census mismatch')
    return manifest, archive


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--action', choices=['check', 'harvest', 'restricted-harvest', 'aliases', 'folds'], default='check')
    parser.add_argument('--contexts', choices=['unrestricted', 'restricted'], default='restricted')
    parser.add_argument('--radius', type=int, default=4)
    parser.add_argument('--depth', type=int, default=12)
    parser.add_argument('--limit', type=int, default=71)
    parser.add_argument('--include-initial', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    manifest, archive = check()
    if args.action == 'check':
        result = {'status': 'SOURCE_CONTEXT_DEPENDENCIES_PASS',
                  'hash_bound_files': len(manifest['files']),
                  'scope': 'Exact archived data/dependencies and recorded census only; no fresh runtime or search.'}
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result, indent=2))
        return
    need(args.output is not None, 'Execution requires an explicit --output path')
    output = args.output.resolve()
    need(ROOT not in output.parents and output != ROOT,
         'Choose an output outside the sealed delivery directory')
    if args.action in ('harvest', 'restricted-harvest'):
        need(__debug__ and not sys.flags.optimize, 'Runtime rederivation requires enabled assertions')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='u208-source-contexts-') as temp:
        work = Path(temp)
        shutil.copytree(HERE / 'original_code/comparison_research', work / 'comparison_research')
        staging = work / manifest['source_archive']['staging_path']
        staging.mkdir(parents=True)
        with zipfile.ZipFile(archive) as bundle:
            for info in bundle.infolist():
                path = Path(info.filename)
                need(not path.is_absolute() and '..' not in path.parts, 'Unsafe archive entry')
            bundle.extractall(staging)
        (work / 'logic_audit').mkdir()
        shutil.copyfile(HERE / 'facts/source_intervals.json', work / 'logic_audit/source_intervals.json')
        if args.action in ('harvest', 'restricted-harvest'):
            script = 'source_context_harvest.py' if args.action == 'harvest' else 'restricted_context_harvest.py'
            command = [sys.executable, '-B', str(work / 'comparison_research' / script),
                       '--radius', str(args.radius), '--output', str(output)]
        else:
            filename = 'source_contexts208_r4.json' if args.contexts == 'unrestricted' else 'restricted_contexts208_r4.json'
            command = [sys.executable, '-B', str(work / 'comparison_research/source_context_fold_search.py'),
                       str(HERE / 'data' / filename), '--mode', args.action,
                       '--limit', str(args.limit), '--history-depth', str(args.depth),
                       '--output', str(output)]
            if args.include_initial:
                command.append('--include-initial')
        subprocess.run(command, cwd=work, check=True)


if __name__ == '__main__':
    main()
