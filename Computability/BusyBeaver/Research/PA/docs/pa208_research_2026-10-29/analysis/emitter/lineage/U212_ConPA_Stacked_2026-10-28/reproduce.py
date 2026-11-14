#!/usr/bin/env python3
"""Offline construction, local proof audit, comparison, and optional full runtime."""
import argparse
import gzip
import hashlib
import json
import subprocess
import sys
import tempfile
import time
import zipfile
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'code'))
from build import construct, digest, need, parse, validate, SOURCE_SHA
import check_local_independent
import check_comparison

PARENT_ARCHIVE_SHA = '09e869763555e19d73f1b7900eee7305105ee02219196dcc88bb6854f34d7f29'

def manifest():
    names = []
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        sha, name = line.split('  ', 1)
        path = (ROOT / name).resolve()
        need(path.is_relative_to(ROOT) and path.is_file(), 'manifest path')
        need(digest(path.read_bytes()) == sha, 'manifest mismatch: ' + name)
        names.append(name)
    need(len(names) == len(set(names)), 'duplicate manifest entry')
    return len(names)

def parent_binding(work, full):
    archive = ROOT / 'inputs/parent_U213_ConPA_2026-10-28_1.zip'
    need(digest(archive.read_bytes()) == PARENT_ARCHIVE_SHA, 'parent archive identity')
    with zipfile.ZipFile(archive) as stream:
        prefix = 'U213_ConPA_2026-10-28/'
        for child, parent in [('inputs/parent213.native.tm', 'machine/u213.native.tm'),
                              ('machine/sites.json', 'machine/sites.json'),
                              ('inputs/legacy_mapping.json', 'inputs/legacy_mapping.json')]:
            need((ROOT / child).read_bytes() == stream.read(prefix + parent), 'parent binding')
        for name in ['symbolic_runtime.py', 'independent_runtime.py', 'source_language.py']:
            need((ROOT / 'code/vendor' / name).read_bytes() == stream.read(prefix + 'code/' + name),
                 'runtime helper differs from parent: ' + name)
        target = work / 'parent'
        target.mkdir()
        for item in stream.infolist():
            need((target / item.filename).resolve().is_relative_to(target.resolve()), 'unsafe ZIP path')
        stream.extractall(target)
    parent = target / 'U213_ConPA_2026-10-28'
    args = [sys.executable, '-B', str(parent / 'reproduce.py'), '--report', str(work / 'parent.json')]
    if full:
        args.append('--full')
    result = subprocess.run(args, cwd=parent, text=True, capture_output=True)
    (work / 'parent.log').write_text(result.stdout + result.stderr)
    need(result.returncode == 0, 'parent replay failed: ' + result.stderr[-2000:])
    receipt = json.loads((work / 'parent.json').read_text())
    expected = 'U213_FULL_REPLAY_PASS' if full else 'U213_FINITE_REPLAY_PASS'
    need(receipt['status'] == expected, 'parent replay status')
    return {'archive_sha256': PARENT_ARCHIVE_SHA, 'status': receipt['status'],
            'full_runtime_rederived': full, 'inherited_parent': receipt['parent'],
            'source_primitives': receipt['source_primitives'],
            'source_subtrees': receipt['source_subtrees'],
            'source_semantic_occurrences_bound': receipt['source_semantic_occurrences_bound']}

def frozen_runtime():
    report = json.loads((ROOT / 'evidence/runtime.json').read_text())
    with gzip.open(ROOT / 'evidence/runtime_cases.json.gz', 'rt') as stream:
        cases = json.load(stream)
    sites = json.loads((ROOT / 'machine/sites.json').read_text())
    expected = [(i, guard) for i, (_, op, _) in enumerate(sites)
                for guard in ((False, True) if op == 'CD' else (False,))]
    need([(c['site_index'], c['positive']) for c in cases] == expected, 'saved case coverage')
    need(report['cases'] == len(cases) == 5084 and report['row_coverage'] == 424,
         'saved runtime census')
    need(report['table_sha256'] == digest((ROOT / 'machine/u212.native.tm').read_bytes()),
         'saved table binding')
    need(report['source_sha256'] == SOURCE_SHA, 'saved source binding')
    need(report['checker_sha256'] == digest((ROOT / 'code/vendor/symbolic_runtime.py').read_bytes()),
         'saved checker binding')
    need(sum(c['symbolic_steps'] for c in cases) == report['symbolic_steps'], 'saved inference count')
    need(all(len(c['duration']) == 13 and c['duration'][0] > 0
             and all(n >= 0 for n in c['duration']) for c in cases), 'saved duration shape')
    return {'cases': len(cases), 'rows': 424, 'symbolic_steps': report['symbolic_steps'],
            'minimum_duration_constant': report['minimum_duration_constant']}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true', help='rederive every U212 symbolic contract')
    parser.add_argument('--parent-full', action='store_true', help='also rederive all parent U213 contracts')
    parser.add_argument('--report', type=Path, help='write a receipt outside the sealed package')
    args = parser.parse_args()
    need(__debug__ and not sys.flags.optimize, 'Run without -O or PYTHONOPTIMIZE')
    start = time.monotonic()
    file_count = manifest()
    with tempfile.TemporaryDirectory(prefix='u212-replay-') as directory:
        work = Path(directory)
        summary = construct(ROOT / 'inputs/parent213.native.tm', work / 'machine')
        for name in ['u212.native.tm', 'u212.tm', 'stage1.native.tm', 'state_map.json', 'summary.json']:
            need((work / 'machine' / name).read_bytes() == (ROOT / 'machine' / name).read_bytes(),
                 'reconstructed bytes differ: ' + name)
        local = check_local_independent.run(ROOT / 'inputs/parent213.native.tm',
                                            ROOT / 'machine/u212.native.tm')
        local = json.loads(json.dumps(local))
        need(local == json.loads((ROOT / 'evidence/independent_audit.json').read_text()),
             'local/startup receipt differs')
        comparison = check_comparison.run()
        frozen = frozen_runtime()
        parent = parent_binding(work, args.parent_full)
        runtime = None
        if args.full:
            from check_runtime import run
            runtime = run(work / 'runtime')
        result = {'status': 'U212_FULL_REPLAY_PASS' if args.full else 'U212_FINITE_REPLAY_PASS',
                  'manifest_files': file_count, 'construction': summary,
                  'local_universal_path_cases': len(local['exact_paths']),
                  'semantic_negative_controls_rejected': len(local['semantic_negative_controls_rejected']),
                  'startup_steps': local['blank_prefix']['steps'],
                  'startup_edited_row_visits': local['blank_prefix']['modified_row_visits'],
                  'comparison_status': comparison['status'], 'frozen_runtime': frozen,
                  'runtime_contracts_rederived': 5084 if runtime else 0,
                  'parent': parent, 'seconds': round(time.monotonic() - start, 3),
                  'scope': 'Exact construction, finite path proof and startup, eight-proposal comparison; '
                           '--full rederives unary/list-inductive runtime contracts. '
                           'Inherited U/PA calibration is ordinary mathematics, not a new kernel certificate.'}
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
