#!/usr/bin/env python3
"""Reconstruct and independently check the new primary 215-state candidate.

Standard library only; no network or solver. Default: exact construction,
source bisimulation, complete native/canonical dense startup, both all-tape
local folds, and complete stored runtime inventory. --runtime freshly derives
all 6,176 arbitrary-natural primitive cases using the pinned inherited engine.
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent
PARENT = 'K216_Partial_Selector_2026-10-20'
RUNTIME_PINS = {
    'validate_native.py': '49b0a77bafa3549cef72e381352eeadad28937519ec5463c3cf3bee545f6f7e2',
    'runtime/symbolic_runtime.py': '7ca30fd11def00e973d8f30997e51fa2dd87ae2eff311ea8c9fc4ac08c9d774f',
    'runtime/independent_runtime.py': '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
    'inputs/legacy_mapping.json': '26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf',
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def readz(path):
    return json.loads(gzip.decompress(path.read_bytes()))


def run(script, arguments, log):
    with log.open('w') as stream:
        proc = subprocess.run([sys.executable, '-B', str(script), *map(str, arguments)],
                              stdout=stream, stderr=subprocess.STDOUT)
    if proc.returncode:
        raise RuntimeError(f'{script.name} failed:\n' + log.read_text()[-12000:])


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without -O or PYTHONOPTIMIZE; assertions must remain enabled.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True, help='New output directory outside the pinned packet')
    ap.add_argument('--runtime', action='store_true', help='Freshly derive every universal primitive case')
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    run(HERE / 'build.py', ['--output', out / 'construction'], out / 'construction.log')
    construction = json.loads((out / 'construction/construction.json').read_text())
    primary = construction['machines'][0]
    assert primary['working_states'] == 215 and primary['rows'] == 430
    assert primary['native_sha256'] == '04b4dbb537306f40f8965ad6a0ee6034e9953f079c233153e9696acdf06c2712'
    assert primary['canonical_sha256'] == '6c0fff966c4409eb726e634d6d5753552e198da0f8c7bfe7fc39ec0151f1de7a'
    archive = HERE / 'parents' / (PARENT + '.zip')
    raw = archive.read_bytes()
    assert sha(raw) == '05c4e63b64e64426fe1c909c0cd2490146fe13805b51f5016b6ff9dd8748ebcc'
    engine = out / 'pinned-runtime'
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        for name, expected in RUNTIME_PINS.items():
            data = z.read(PARENT + '/code/' + name)
            assert sha(data) == expected, name
            target = engine / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    table = HERE / 'k215.native.tm'
    source = HERE / 'sites215.json'
    run(HERE / 'review/review_source_bisimulation215.py',
        ['--reference', HERE / 'inputs/permuted210.sites.json', '--candidate', source,
         '--output', out / 'independent-source.json'], out / 'independent-source.log')
    run(HERE / 'review/review_composition215.py',
        ['--table', table, '--canonical', HERE / 'k215.tm',
         '--partial', HERE / 'inputs/partial216.native.tm',
         '--k217', PACKET / 'baseline/k217.native.tm',
         '--startup', HERE / 'fresh/startup.json.gz',
         '--output', out / 'independent-physical.json', '--work', out / 'unfolded'],
        out / 'independent-physical.log')
    run(HERE / 'review/review_runtime_inventory215.py',
        ['--table', table, '--source', source, '--runtime', HERE / 'fresh/runtime.json',
         '--cases', HERE / 'fresh/runtime_cases.json.gz',
         '--mapping', engine / 'inputs/legacy_mapping.json',
         '--output', out / 'independent-runtime-inventory.json'], out / 'runtime-inventory.log')
    for label, old, new, keep, drop in [
        ('first', out / 'unfolded/unfolded217.native.tm', out / 'unfolded/unfolded216.native.tm', 69, 400),
        ('second', out / 'unfolded/unfolded216.native.tm', table, 164, 183),
    ]:
        run(PACKET / 'search/physical/check_joint_fold.py',
            ['--old', old, '--new', new, '--keep', keep, '--drop', drop,
             '--radius', 4, '--fuel', 20, '--output', out / (label + '-local-fold.json')],
            out / (label + '-local-fold.log'))
        fold = json.loads((out / (label + '-local-fold.json')).read_text())
        assert fold['status'] == 'INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'
        assert fold['negative_control']['status'] == 'REJECTED'
    inventory = json.loads((out / 'independent-runtime-inventory.json').read_text())
    assert inventory['guarded_cases'] == 6176 and inventory['directly_used_native_rows'] == 430
    assert inventory['symbolic_steps'] == 1698790 and inventory['minimum_positive_constant'] == 6
    if args.runtime:
        run(engine / 'validate_native.py', [table, source, out / 'universal-runtime'], out / 'universal-runtime.log')
        fresh = json.loads((out / 'universal-runtime/runtime.json').read_text())
        assert fresh['status'] == 'UNIVERSAL_MATHEMATICAL_PASS' and not fresh['failures']
        assert fresh['proved_cases'] == fresh['expected_cases'] == 6176
        assert fresh['checker_sha256'] == RUNTIME_PINS['runtime/symbolic_runtime.py']
        assert fresh['helper_sha256'] == RUNTIME_PINS['runtime/independent_runtime.py']
        assert json.loads((out / 'universal-runtime/runtime_cases.json').read_text()) == readz(HERE / 'fresh/runtime_cases.json.gz')
        assert json.loads((out / 'universal-runtime/startup.json').read_text()) == readz(HERE / 'fresh/startup.json.gz')
    result = {
        'status': 'NEW_K215_COMPOSITION_CHECKS_PASS', 'working_states': 215, 'rows': 430,
        'native_sha256': primary['native_sha256'], 'canonical_sha256': primary['canonical_sha256'],
        'source_sha256': primary['source_sha256'],
        'guarded_cases': 6176, 'symbolic_rules': 1698790, 'all_transition_rows_used': 430,
        'minimum_positive_affine_constant': 6, 'complete_blank_steps': 95726,
        'fresh_full_runtime_this_replay': args.runtime,
        'construction': 'New constrained composition of the credited public Partial Selector and Permuted Commands K216 constructions.',
        'scope': 'Exact construction, all-natural source bisimulation, complete finite blank trace, local all-tape folds, and ordered runtime inventory. --runtime additionally rederives all universal cases. Foundational native-calculus/ZFC calibration is an inherited pinned mathematical dependency; no new proof-assistant endpoint.',
        'runtime_dependencies': RUNTIME_PINS,
    }
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
