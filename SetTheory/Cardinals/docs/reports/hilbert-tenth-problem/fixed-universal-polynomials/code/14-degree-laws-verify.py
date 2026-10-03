#!/usr/bin/env python3
"""Run the self-contained exact-degree checks; optionally replay the universal DAG."""
import sys
sys.dontwritebytecode = True
import argparse
import ast
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
RESEARCH_MANIFEST_SHA256 = '98c30210fd431f9bb717a8b8e5bd13a1a57f89a48c89a21ee007ec16a4da1607'
RESEARCH_MANIFEST_CONTENT_SHA256 = '01528e3ea6caf46ac27919395ab793842dfd810a0e8a1e9b27c306dd3dadf2ac'
CHECKS = (
    ('check_native_law.py', 'independent_certificate.json', ('--skip-full',)),
    ('check_diagonal_expansion.py', 'diagonal_expansion_certificate.json', ()),
    ('review_extensions.py', 'extension_review_certificate.json', ()),
    ('check_loader_degrees.py', 'loader_degree_certificate.json', ()),
)


def need(value, message):
    if not value:
        raise RuntimeError(message)


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(path.read_text(encoding='utf-8'))


def relative(name):
    p = PurePosixPath(name)
    need(isinstance(name, str) and name and not p.is_absolute() and
         '..' not in p.parts and '.' not in p.parts and str(p) == name,
         'Unsafe inventory route')
    return name


def snapshot(root):
    files = {}
    directories = []
    need(root.is_dir() and not root.is_symlink(), 'Missing or symlinked package')
    for path in sorted(root.rglob('*')):
        name = path.relative_to(root).as_posix()
        need(not path.is_symlink(), 'Symlink is forbidden: ' + name)
        if path.is_dir():
            directories.append(name)
        else:
            need(path.is_file(), 'Nonregular package entry: ' + name)
            files[name] = {'bytes': path.stat().st_size, 'sha256': sha(path)}
    return {'files': files, 'directories': directories}


def normalized(value):
    if isinstance(value, dict):
        return {k: normalized(v) for k, v in value.items()
                if k not in ('elapsed_seconds', 'seconds')}
    if isinstance(value, list):
        return [normalized(v) for v in value]
    return value


def verify_integrity(root=ROOT):
    root = Path(root)
    current = snapshot(root)
    need((root / 'INVENTORY.json').is_file() and (root / 'INVENTORY.sha256').is_file(),
         'Missing mandatory inventory or digest')
    anchor = (root / 'INVENTORY.sha256').read_text(encoding='ascii')
    need(len(anchor) == 65 and anchor[-1] == '\n' and
         all(c in '0123456789abcdef' for c in anchor[:-1]), 'Malformed inventory digest')
    need(sha(root / 'INVENTORY.json') == anchor.strip(), 'Inventory digest mismatch')
    inv = read(root / 'INVENTORY.json')
    need(inv['schema'] == 'native-degree-law-inventory-v1', 'Inventory schema mismatch')
    actual = {k: v for k, v in current['files'].items()
              if k not in ('INVENTORY.json', 'INVENTORY.sha256')}
    need(set(actual) == set(inv['files']), 'Exact inventory file-set mismatch; missing=' +
         repr(sorted(set(inv['files']) - set(actual))) + '; extra=' +
         repr(sorted(set(actual) - set(inv['files']))))
    need(current['directories'] == inv['directories'], 'Exact directory inventory mismatch')
    for name, item in inv['files'].items():
        relative(name)
        need(actual[name] == item, 'Content digest mismatch: ' + name)
    prov = read(root / 'PROVENANCE.json')
    need(prov['schema'] == 'native-degree-law-provenance-v1', 'Provenance schema mismatch')
    need(prov['frozen_research_manifest_sha256'] == RESEARCH_MANIFEST_SHA256,
         'Original research-manifest provenance anchor mismatch')
    manifest_records = [item for item in prov['records']
                        if item['delivered'] == 'research/MANIFEST.json']
    need(len(manifest_records) == 1 and
         manifest_records[0]['original_sha256'] == RESEARCH_MANIFEST_SHA256 and
         manifest_records[0]['portable_sha256'] == sha(root / 'research/MANIFEST.json'),
         'Original/portable research-manifest provenance mismatch')
    research = read(root / 'research/MANIFEST.json')
    need(research['publication_status'] == 'frozen research reference',
         'Portable research-manifest status mismatch')
    manifest_content = {key: value for key, value in research.items()
                        if key != 'publication_status'}
    content_digest = hashlib.sha256(json.dumps(manifest_content, sort_keys=True,
                                   separators=(',', ':')).encode('utf-8')).hexdigest()
    need(content_digest == RESEARCH_MANIFEST_CONTENT_SHA256 ==
         prov['frozen_research_manifest_content_sha256'],
         'Original scientific manifest entries or pins changed')
    originals = {'research/' + e['path']: e for e in research['files']}
    seen = set()
    for item in prov['records']:
        name = relative(item['delivered'])
        need(name not in seen, 'Duplicate provenance destination')
        seen.add(name)
        need(current['files'][name] == {'bytes': item['portable_bytes'],
             'sha256': item['portable_sha256']}, 'Portable provenance mismatch: ' + name)
        if item['origin'] in originals:
            original = originals[item['origin']]
            need(item['original_sha256'] == original['sha256'] and
                 item['original_bytes'] == original['bytes'], 'Original research provenance mismatch')
        if item['byte_identical']:
            need(item['original_sha256'] == item['portable_sha256'] and
                 item['original_bytes'] == item['portable_bytes'], 'False byte-identity claim')
    expected_provenance = {name for name in current['files']
                           if name.split('/')[0] in ('data', 'research', 'certificates', 'checks')}
    need(seen == expected_provenance, 'Incomplete provenance coverage')
    data_pins = read(root / 'INPUT_PINS.json')
    need(set(data_pins) == {name[5:] for name in current['files'] if name.startswith('data/')},
         'Missing or extra mandatory input pin')
    for name, pin in data_pins.items():
        need(sha(root / 'data' / relative(name)) == pin, 'Mandatory input pin mismatch: ' + name)
    need(data_pins['native_history_proof.md'] == research['source_pins']['native_history_proof.md'],
         'Native proof pin mismatch')
    need(not list((root / 'data').rglob('*.py')) and not list((root / 'research').rglob('*.py')),
         'Original Python must remain inert .py.txt data')
    for path in root.rglob('*.py'):
        tree = ast.parse(path.read_text(encoding='utf-8'))
        need(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)),
             'Optimization-sensitive assertion: ' + path.name)
    for basename in ('independent_certificate', 'diagonal_expansion_certificate', 'loader_degree_certificate'):
        need(normalized(read(root / 'certificates' / (basename + '.json'))) ==
             normalized(read(root / 'certificates' / (basename + '_optimized.json'))),
             'Normal/optimized research certificate mismatch: ' + basename)
    return {'status': 'PASS', 'file_count': len(current['files']),
            'directory_count': len(current['directories']), 'inventory_sha256': anchor.strip(),
            'mandatory_input_pins': len(data_pins), 'provenance_records': len(seen)}


def core():
    results = []
    with tempfile.TemporaryDirectory(prefix='degree-law-check-') as work:
        for script, certificate, extra in CHECKS:
            output = Path(work) / certificate
            command = [sys.executable, '-B']
            if sys.flags.optimize:
                command.append('-O')
            command += [str(ROOT / 'checks' / script), '--source-dir', str(ROOT / 'data'),
                        '--output', str(output), *extra]
            proc = subprocess.run(command, cwd=work, text=True, capture_output=True,
                                  env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
            need(proc.returncode == 0, 'Checker failed: ' + script + '; exit=' + str(proc.returncode))
            need(output.is_file(), 'Checker did not produce its certificate: ' + script)
            actual = read(output)
            expected = read(ROOT / 'certificates' / certificate)
            if script == 'check_native_law.py':
                expected['files'] = [f for f in expected['files'] if f['source'] != 'universal.dag']
            need(normalized(actual) == normalized(expected), 'Scientific certificate mismatch: ' + script)
            results.append({'checker': script, 'status': 'PASS', 'matches_frozen_certificate': True})
    return results


def universal(source_dir):
    source_dir = Path(source_dir).resolve()
    need(source_dir.is_dir(), 'Explicit universal source directory is missing')
    expected = read(ROOT / 'PROVENANCE.json')['optional_report23v1_source']['source_files']
    pins = {}
    # The documented Report23 v1 frozen/arithmetic layout is used exactly.
    # There is no source search and no alternate filename fallback.
    for logical, pin in expected.items():
        name = logical + '.txt' if logical.endswith('.py') else logical
        path = source_dir / name
        need(path.is_file() and not path.is_symlink(), 'Missing mandatory universal input: ' + name)
        need(sha(path) == pin, 'Universal source pin mismatch: ' + name)
        pins[name] = pin
    spec = importlib.util.spec_from_file_location('portable_native_checker', ROOT / 'checks/check_native_law.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.SRC = source_dir
    identity = module.identity_check()
    kernel = read(source_dir / 'native_unit_kernel.json')
    actual = module.check_file('universal', kernel)
    reference = read(ROOT / 'certificates/independent_certificate.json')
    expected_file = [f for f in reference['files'] if f['source'] == 'universal.dag']
    need(len(expected_file) == 1 and actual == expected_file[0], 'Universal scientific certificate mismatch')
    need(json.loads(json.dumps(identity)) == reference['R15_identity'], 'Universal identity certificate mismatch')
    for name, pin in pins.items():
        need(sha(source_dir / name) == pin, 'Universal source changed during replay: ' + name)
    return {'status': 'PASS', 'm': actual['m'], 'g': actual['g'], 'N': actual['N'],
            'nodes': actual['nodes'], 'exact_degree': actual['exact_degree'],
            'modular_leading_coefficients': [p['output']['diagonal_coefficient'] for p in actual['passes']],
            'mandatory_source_pins': len(pins), 'source_files_unchanged': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--integrity-only', action='store_true', help='verify exact inventory, pins and provenance only')
    parser.add_argument('--universal', action='store_true', help='also replay the large frozen universal DAG')
    parser.add_argument('--source-dir', type=Path, help='explicit Report23 v1 reproducibility/frozen/arithmetic directory')
    parser.add_argument('--output', type=Path, help='optional JSON receipt outside this reproducibility directory')
    args = parser.parse_args()
    need(args.universal == (args.source_dir is not None),
         '--universal and an explicit --source-dir must be supplied together')
    need(not (args.integrity_only and args.universal), '--integrity-only cannot be combined with --universal')
    if args.output:
        output = args.output.resolve()
        need(output != ROOT and ROOT not in output.parents, 'Output must be outside this reproducibility directory')
    before = snapshot(ROOT)
    result = {'status': 'PASS', 'mode': 'integrity-only' if args.integrity_only else 'core+universal' if args.universal else 'core',
              'integrity': verify_integrity(), 'python_optimized': bool(sys.flags.optimize),
              'upstream_python_executed': False}
    if not args.integrity_only:
        result['checks'] = core()
    if args.universal:
        result['universal'] = universal(args.source_dir)
    need(snapshot(ROOT) == before, 'Package inventory changed during verification')
    result['package_inventory_unchanged'] = True
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc).replace(str(ROOT), '.')}), file=sys.stderr)
        sys.exit(1)
