#!/usr/bin/env python3
"""Verify and replay the exact-degree extension using only sibling frozen data."""
import sys
sys.dontwritebytecode = True
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
HISTORICAL_INVENTORY_SHA256 = '95940bfa3ff6fba747fe2252b3ae8ac89e9633355a341cf6787b4b27cb85151e'
PINS = {
    'universal.dag': 'a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2',
    'universal.json': '41e6f754df8f60448e1207ef36e6161729b52004fac719a580d6ec643d039d49',
    'native_unit_kernel.json': '2d88343037c08fe8b073f67dca531ee73309c0735c1d98a23c20b9ddb1eb08ae',
}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def safe_relative(name):
    need(type(name) is str and name != '', 'Missing relative file route')
    p = PurePosixPath(name)
    need(not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and str(p) == name,
         'Invalid relative file route: ' + name)
    return name


def verify_tree(root, schema, expected_anchor=None):
    root = Path(root)
    need(root.is_dir() and not root.is_symlink(), 'Missing or symlinked package directory')
    files, directories = set(), set()
    for path in root.rglob('*'):
        name = path.relative_to(root).as_posix()
        need(not path.is_symlink(), 'Symlink forbidden: ' + name)
        if path.is_dir():
            directories.add(name)
        else:
            need(path.is_file(), 'Nonregular entry: ' + name)
            files.add(name)
    anchor = (root / 'INVENTORY.sha256').read_text(encoding='ascii')
    need(len(anchor) == 65 and anchor[-1] == '\n' and all(c in '0123456789abcdef' for c in anchor[:-1]),
         'Malformed inventory anchor')
    if expected_anchor is not None:
        need(anchor.strip() == expected_anchor, 'Historical inventory anchor changed')
    need(digest(root / 'INVENTORY.json') == anchor.strip(), 'Inventory digest mismatch')
    inventory = read_json(root / 'INVENTORY.json')
    need(inventory['schema'] == schema, 'Inventory schema mismatch')
    expected = set(inventory['files']) | {'INVENTORY.json', 'INVENTORY.sha256'}
    need(files == expected, 'Inventory file-set mismatch; missing=' + repr(sorted(expected-files)) +
         '; extra=' + repr(sorted(files-expected)))
    need(directories == set(inventory['directories']), 'Inventory directory-set mismatch')
    for name, item in inventory['files'].items():
        path = root / safe_relative(name)
        need(type(item['bytes']) is int and path.stat().st_size == item['bytes'] and digest(path) == item['sha256'],
             'Content digest mismatch: ' + name)
    return {'status': 'PASS_EXACT_INVENTORY', 'files': len(files), 'directories': len(directories),
            'inventory_sha256': anchor.strip()}


def verify_extension(root=ROOT):
    root = Path(root)
    receipt = verify_tree(root, 'grill-exact-degree-inventory-v1')
    provenance = read_json(root / 'PROVENANCE.json')
    need(provenance['schema'] == 'grill-exact-degree-provenance-v1', 'Provenance schema mismatch')
    delivered, sources = set(), set()
    for item in provenance['sources']:
        name = safe_relative(item['delivered'])
        need(name not in delivered and item['source'] not in sources, 'Duplicate provenance entry')
        delivered.add(name)
        sources.add(item['source'])
        path = root / name
        need(path.stat().st_size == item['delivered_bytes'] and digest(path) == item['delivered_sha256'],
             'Delivered provenance mismatch: ' + name)
        if item['byte_identical']:
            need(item['original_bytes'] == item['delivered_bytes'] and
                 item['original_sha256'] == item['delivered_sha256'], 'False byte-identity claim')
    need(delivered == {p.relative_to(root).as_posix() for p in (root / 'frozen').rglob('*') if p.is_file()},
         'Provenance does not cover exactly the frozen evidence')
    need(not list((root / 'frozen').rglob('*.py')), 'Frozen original Python must remain inert .py.txt')
    for path in root.rglob('*.py'):
        need(not any(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(path.read_text(encoding='utf-8')))),
             'Removable assertion in executable local code: ' + path.relative_to(root).as_posix())
    # Original receipts identify original local checker bytes, not a sanitized copy.
    originals = {entry['source']: entry for entry in provenance['sources']}
    for name in ('degree_certificate.json', 'degree_certificate_optimized.json'):
        need(read_json(root / 'frozen' / name)['checker_sha256'] == originals['degree/check_degree.py']['original_sha256'],
             'Frozen modular certificate checker provenance mismatch')
    for name in ('independent_leading_result.json', 'independent_leading_result_optimized.json'):
        path = root / 'frozen/independent-review' / name
        need(read_json(path)['checker_sha256'] == originals['degree/independent-review/check_leading.py']['original_sha256'],
             'Frozen symbolic certificate checker provenance mismatch')
    manifest = read_json(root / 'frozen/MANIFEST.json')
    need(manifest['status'] == 'FROZEN_PASS' and manifest['file_count'] == len(manifest['files']),
         'Research freeze manifest mismatch')
    need(digest(root / 'frozen/MANIFEST.json') == provenance['frozen_source_manifest_sha256'],
         'Research freeze anchor mismatch')
    need({'degree/' + entry['path'] for entry in manifest['files']} | {'degree/MANIFEST.json'} == set(originals),
         'Original source inventory mismatch')
    for entry in manifest['files']:
        original = originals['degree/' + entry['path']]
        need(entry['bytes'] == original['original_bytes'] and entry['sha256'] == original['original_sha256'],
             'Research original hash mismatch: ' + entry['path'])
    for entry in provenance['executable_adaptations']:
        need(entry['original_sha256'] == originals[entry['source']]['original_sha256'] and
             digest(root / safe_relative(entry['delivered'])) == entry['delivered_sha256'],
             'Executable adaptation provenance mismatch')
    return receipt


def verify_dependencies(root=ROOT):
    root = Path(root)
    base = root.parent / 'reproducibility'
    receipt = verify_tree(base, 'grill-exact-inventory-v1', HISTORICAL_INVENTORY_SHA256)
    source = base / 'frozen/arithmetic'
    for name, pin in PINS.items():
        need(digest(source / name) == pin, 'Pinned arithmetic mismatch: ' + name)
    receipt['status'] = 'PASS_UNCHANGED_HISTORICAL_REPRODUCIBILITY'
    receipt['source_pins'] = PINS
    return receipt


def scientific(certificate, kind):
    result = json.loads(json.dumps(certificate))
    result.pop('checker_sha256', None)
    result.pop('resources', None)
    if kind == 'symbolic':
        result.pop('scan_seconds', None)
    return result


def validate_certificates(modular, symbolic):
    need(modular['status'] == 'PASS' and modular['total_degree'] == 69_339_973,
         'Modular checker did not certify expected exact degree')
    need(modular['previous_syntactic_upper_bound'] == 71_731_007 and modular['decrease'] == 2_391_034,
         'Historical bound relationship mismatch')
    need(modular['source_pins'] == PINS and modular['frozen_kernel_all_67_rows_match'] is True,
         'Modular source binding mismatch')
    need(modular['identity']['exact_dictionary_equality'] is True and modular['identity']['left_monomials'] == 11,
         'Unrestricted polynomial identity missing')
    need([item['modulus'] for item in modular['trials']] == [17, 1_000_000_007], 'Missing modulus certificate')
    for trial, residue in zip(modular['trials'], (3, 53_942_795)):
        need(trial['output']['degree_bound'] == 69_339_973 and trial['output']['leading_value'] == residue and
             trial['closed_form_leading_coefficient'] == residue and trial['exact_degree_certified'] is True,
             'Modular exact-degree certificate mismatch')
    need(symbolic['source_sha256'] == PINS['universal.dag'] and symbolic['complete_exact_degree'] == 69_339_973,
         'Independent exact-degree certificate mismatch')
    need(symbolic['kernel_rows_matched'] == 67 and symbolic['all_shat_inputs_checked_once'] == 794_976,
         'Independent structural check incomplete')
    need(symbolic['top_polynomial_sparse_terms_in_p_and_inputs'] == 23 and
         symbolic['maximal_residual_square_index_zero_based'] == 6 and symbolic['finalizer_exact_degree'] == 19_128_284,
         'Independent homogeneous-form check incomplete')


def replay(work):
    need(not any(work.iterdir()), 'Replay working directory must be empty')
    source = ROOT.parent / 'reproducibility/frozen/arithmetic'
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    environment.pop('PYTHONPATH', None)
    flags = [sys.executable, '-I', '-B'] + (['-O'] if sys.flags.optimize else [])
    receipts = []
    cases = [('modular', 'check_degree.py', 'degree_certificate.json', 'degree_certificate_optimized.json'),
             ('symbolic', 'check_leading.py', 'independent-review/independent_leading_result.json',
              'independent-review/independent_leading_result_optimized.json')]
    regenerated = {}
    for kind, script, frozen_normal, frozen_optimized in cases:
        output = work / (kind + '_certificate.json')
        started = time.monotonic()
        proc = subprocess.run(flags + [str(ROOT / 'replay_code' / script), '--source-dir', str(source),
                                       '--output', str(output)], cwd=work, env=environment,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=210)
        (work / (kind + '.log')).write_text(proc.stdout, encoding='utf-8')
        need(proc.returncode == 0, kind + ' replay failed:\n' + proc.stdout)
        actual = read_json(output)
        need(actual['checker_sha256'] == digest(ROOT / 'replay_code' / script), 'Replay checker hash mismatch')
        for frozen in (frozen_normal, frozen_optimized):
            need(scientific(actual, kind) == scientific(read_json(ROOT / 'frozen' / frozen), kind),
                 'Regenerated scientific certificate differs: ' + frozen)
        regenerated[kind] = actual
        receipt = {'checker': kind, 'status': 'PASS', 'seconds': round(time.monotonic()-started, 3),
                   'scientific_certificate_matches_both_frozen_python_modes': True}
        receipts.append(receipt)
        print(json.dumps(receipt, sort_keys=True), flush=True)
    validate_certificates(regenerated['modular'], regenerated['symbolic'])
    result = {'status': 'PASS_EXACT_DEGREE_REPLAY', 'optimized': bool(sys.flags.optimize),
              'exact_total_degree': 69_339_973, 'historical_upper_bound': 71_731_007,
              'all_supplied_coordinates_degree_one': 797_141, 'source_pins': PINS,
              'modular_residues': {'17': 3, '1000000007': 53_942_795},
              'original_or_upstream_python_executed': False, 'delivered_files_modified': False,
              'checks': receipts}
    (work / 'replay_receipt.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-only', action='store_true')
    parser.add_argument('--work-dir', type=Path, help='Optional EMPTY output directory outside the entire release')
    args = parser.parse_args()
    print(json.dumps(verify_extension(), sort_keys=True), flush=True)
    print(json.dumps(verify_dependencies(), sort_keys=True), flush=True)
    if args.verify_only:
        return
    if args.work_dir:
        work = args.work_dir.expanduser().resolve()
        release = ROOT.parent
        need(work != release and release not in work.parents, 'Outputs must stay outside the complete release')
        work.mkdir(parents=True, exist_ok=True)
        result = replay(work)
    else:
        with tempfile.TemporaryDirectory(prefix='grill-exact-degree-replay-') as directory:
            result = replay(Path(directory))
    print(json.dumps(result, indent=2, sort_keys=True), flush=True)
    verify_extension()
    verify_dependencies()


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
