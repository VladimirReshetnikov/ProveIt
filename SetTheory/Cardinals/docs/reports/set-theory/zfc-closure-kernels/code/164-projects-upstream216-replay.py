#!/usr/bin/env python3
"""Replay the selected checks on the credited late public K216 submission.

No network. The --runtime option freshly derives all 6,176 primitive cases.
The default checks finite construction, both blank interpreters, and the stored
complete ordered runtime inventory. Foundational calibration remains inherited.
"""
import argparse
import gzip
import hashlib
import importlib.util
from io import BytesIO
import json
from pathlib import Path
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent
NAME = 'K216_Permuted_Commands_2026-10-21'
PARENT = 'K217_Dominated_Continuation_2026-10-20'
GRANDPARENT = 'K218_Dominated_Rho8_2026-10-20'
ARCHIVE_SHA = 'c9b9a3355316cf084c86a702cce092fe4ea16bf837e9b258cb1c2fd87ac5a4f3'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def readz(path):
    return json.loads(gzip.decompress(path.read_bytes()))


def run(script, arguments, log):
    with log.open('w') as stream:
        proc = subprocess.run([sys.executable, '-B', str(script), *map(str, arguments)],
                              stdout=stream, stderr=subprocess.STDOUT)
    if proc.returncode:
        raise RuntimeError(log.read_text()[-12000:])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True, help='New output directory')
    ap.add_argument('--runtime', action='store_true')
    args = ap.parse_args()
    assert __debug__ and not sys.flags.optimize, 'Assertions must remain enabled'
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    archive = HERE / (NAME + '.zip')
    assert sha(archive.read_bytes()) == ARCHIVE_SHA
    with zipfile.ZipFile(archive) as z:
        manifest = json.loads(z.read(NAME + '/manifest.json'))
        for name, expected in manifest['files'].items():
            assert sha(z.read(NAME + '/' + name)) == expected, name
        for item in z.infolist():
            target = (out / item.filename).resolve()
            assert target.is_relative_to(out)
            assert (item.external_attr >> 16) & 0o170000 != 0o120000
        z.extractall(out)
    released = out / NAME
    code = released / 'code'
    source = released / 'source'
    machine = released / 'machine'
    baseline = PACKET / 'baseline'
    run(code / 'build_sources.py',
        ['--baseline219', source / 'baseline219.json', '--baseline217', baseline / 'sites217.json',
         '--output', out / 'rebuilt-source'], out / 'source-build.log')
    for fresh, original in [('sites202.json', 'source/frozen202.json'),
                            ('sites210.json', 'machine/sites216.json'),
                            ('sites120.json', 'secondary/sites120.json')]:
        assert (out / 'rebuilt-source' / fresh).read_bytes() == (released / original).read_bytes()
    run(code / 'reconstruct.py', ['--baseline217', baseline / 'k217.native.tm',
                                 '--output', out / 'rebuilt-table'], out / 'table-build.log')
    for fresh, original in [('k216-210.native.tm', 'machine/k216.native.tm'),
                            ('k216-210.tm', 'machine/k216.tm'),
                            ('k216-120.native.tm', 'secondary/k216-120.native.tm'),
                            ('k216-120.tm', 'secondary/k216-120.tm')]:
        assert (out / 'rebuilt-table' / fresh).read_bytes() == (released / original).read_bytes()
    run(code / 'audit_command_permutation.py',
        ['--baseline219', source / 'baseline219.json', '--frozen202', source / 'frozen202.json',
         '--candidate', machine / 'sites216.json', '--permutation', '210',
         '--output', out / 'command-permutation.json'], out / 'command-permutation.log')
    run(code / 'audit_source210.py',
        [source / 'reference205.json', source / 'frozen202.json', machine / 'sites216.json',
         PACKET / 'search/source/vendor/source_language.py', out / 'independent-source.json'],
        out / 'independent-source.log')

    saved_cases = readz(released / 'evidence/runtime_cases.json.gz')
    saved_start = readz(released / 'evidence/startup.json.gz')
    assert saved_cases == readz(HERE / 'fresh/runtime_cases.json.gz')
    assert saved_start == readz(HERE / 'fresh/startup.json.gz')
    sites = json.loads((machine / 'sites216.json').read_text())
    expected = [(i, positive) for i, (_, op, _) in enumerate(sites)
                for positive in ((False, True) if op == 'CD' else (False,))]
    assert [(case['site_index'], case['positive']) for case in saved_cases] == expected
    assert len(saved_cases) == 6176
    assert sum(c['symbolic_steps'] for c in saved_cases) == 1605450
    assert min(c['duration'][0] for c in saved_cases) == 6
    assert all(len(c['duration']) == 13 and c['duration'][0] > 0
               and all(v >= 0 for v in c['duration']) for c in saved_cases)
    assert len({tuple(row) for c in saved_cases for row in c['rows']}) == 432

    spec = importlib.util.spec_from_file_location('late216_literal_audit', machine / 'audit.py')
    auditor = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(auditor)
    endpoint, trace = auditor.simulate(auditor.parse((machine / 'k216.native.tm').read_bytes()), 95674)
    assert trace == saved_start['trace']
    assert endpoint['state'] == 84 and endpoint['head'] == -8
    assert endpoint['one_cells'] == auditor.expected_seed()['one_cells']
    start_file = out / 'startup.json'
    start_file.write_text(json.dumps(saved_start, indent=2) + '\n')
    run(code / 'audit_blank210.py', [machine / 'k216.native.tm', start_file,
                                    out / 'independent-blank.json'], out / 'independent-blank.log')

    if args.runtime:
        parent_bytes = (released / 'parent' / (PARENT + '.zip')).read_bytes()
        assert sha(parent_bytes) == '4aa33f0c4844043d243fb7d01ef316d4b72de641864e5317525f7cfac7f5c809'
        with zipfile.ZipFile(BytesIO(parent_bytes)) as z:
            base_bytes = z.read(PARENT + '/parent/' + GRANDPARENT + '.zip')
        assert sha(base_bytes) == '080b4fe855c109ab77588c01c9e012d9572afa7721682306370ccb2eb22cbea9'
        runtime = out / 'pinned-runtime'
        with zipfile.ZipFile(BytesIO(base_bytes)) as z:
            for name in ['validate_native.py', 'runtime/symbolic_runtime.py',
                         'runtime/independent_runtime.py', 'inputs/legacy_mapping.json']:
                path = runtime / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(z.read(GRANDPARENT + '/binary/code/' + name))
        run(runtime / 'validate_native.py', [machine / 'k216.native.tm', machine / 'sites216.json',
                                             out / 'runtime'], out / 'runtime.log')
        report = json.loads((out / 'runtime/runtime.json').read_text())
        assert report['status'] == 'UNIVERSAL_MATHEMATICAL_PASS'
        assert report['proved_cases'] == report['expected_cases'] == 6176
        assert json.loads((out / 'runtime/runtime_cases.json').read_text()) == saved_cases
        assert json.loads((out / 'runtime/startup.json').read_text()) == saved_start

    result = {'status': 'SELECTED_UPSTREAM_216_CHECKS_PASS', 'working_states': 216, 'rows': 432,
              'fresh_runtime': args.runtime, 'ordered_cases_checked': 6176,
              'fresh_sparse_and_dense_blank_steps': 95674,
              'canonical_sha256': sha((machine / 'k216.tm').read_bytes()),
              'construction_authorship': 'Credited late upstream submission; not a new table discovered here.',
              'scope': 'Selected finite reconstruction/source/blank checks and complete stored runtime inventory; fresh universal runtime only with --runtime. Foundational calibration remains inherited.'}
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
