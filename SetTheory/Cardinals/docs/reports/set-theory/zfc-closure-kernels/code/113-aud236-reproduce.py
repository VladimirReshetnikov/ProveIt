#!/usr/bin/env python3
"""Offline replay of the236 audit and new logical/encoding supplement.

Validates manifest and pins before creating an isolated temporary work copy.
Quick: finite proofs, source and affine checks, incoming236 quick replay,
and an audit of all stored unbounded case arrays. --full also recomputes
the reassociated237 and final236 complete symbolic runtimes. No discovery
search, external theorem prover, network, or third-party library is required.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import traceback
import zipfile

ROOT = Path(__file__).resolve().parent
PINS = {
    'baseline/zfc_composed237.tm': '7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6',
    'baseline/zfc_composed237_old.tm': 'a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a',
    'machines/zfc_rotated237_old.tm': 'da0b3d1fdd74d56482b9d231119bbbaccdbcadc78e7b7df72c3a734a3a808724',
    'machines/zfc236_old.tm': 'ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3',
    'machines/zfc236.tm': 'd4302309401891d68b93c393e4ad6e24d2abf993dede4a61baa2d3e0c1c53c8e',
    'inputs/source.json': '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6',
    'machines/sites_logical236.json': '1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f',
    'upstream/ZFC236_Construction_2026-10-19.zip': '540305f4e805165e818290e82c5a6cba5faed25b5abb946fd9c750f6c45db9f5',
}


def require(test, why):
    if not test:
        raise ValueError(why)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2)+'\n')


def check_manifest(root):
    entries = {}
    for line in (root/'SHA256SUMS').read_text().splitlines():
        if not line:
            continue
        h, name = line.split('  ', 1)
        p = Path(name)
        require(len(h) == 64 and all(c in '0123456789abcdef' for c in h), 'Malformed hash')
        require(not p.is_absolute() and '..' not in p.parts and name not in entries, 'Unsafe manifest path')
        require((root/p).is_file() and not (root/p).is_symlink(), 'Missing or linked artifact '+name)
        require(digest(root/p) == h, 'Manifest mismatch '+name)
        entries[name] = h
    require(set(PINS) <= set(entries), 'Manifest omits pinned inputs')
    for name, h in PINS.items():
        require(entries[name] == h, 'Pin mismatch '+name)
    for name in ['reproduce.py', 'report.tex', 'report.pdf',
                 'theory/formalism_proofs.py', 'equational667/build_e667.py',
                 'verification/check_affine_dual.py', 'verification/check_literal_runtime236.py']:
        require(name in entries, 'Manifest omits critical artifact '+name)
    return entries


def parse_table(path):
    table, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            require(start is None, 'Duplicate start declaration')
            start = int(line[9:])
        elif line and not line.startswith('#'):
            fields = line.split()
            require(len(fields) == 5, 'Malformed row')
            q, b, w, move, z = fields
            key = int(q), int(b)
            require(key not in table, 'Duplicate row')
            require(int(b) in (0, 1) and int(w) in (0, 1) and move in ('L', 'R'), 'Wrong machine model')
            table[key] = int(w), move, int(z)
    states = {q for q, b in table}
    require(start in states and set(table) == {(q, b) for q in states for b in (0, 1)}, 'Incomplete table')
    return table, start


def check_numbering(root):
    old, oldstart = parse_table(root/'machines/zfc236_old.tm')
    new, newstart = parse_table(root/'machines/zfc236.tm')
    mapping = {int(k): v for k, v in read(root/'machines/renumbering236.json')['old_to_new'].items()}
    require(len(old) == len(new) == 472 and (oldstart, newstart) == (95, 0), 'Wrong236 census')
    require({q for q, b in new} == set(range(236)), 'Wrong canonical working states')
    require({z for w, d, z in new.values()} - set(range(236)) == {236}, 'Wrong canonical halt')
    require(mapping[95] == 0 and mapping[96] == 84 and mapping[254] == 236, 'Wrong control numbering')
    require(len(set(mapping.values())) == len(mapping), 'Noninjective numbering')
    expected = {(mapping[q], b): (w, d, mapping[z]) for (q, b), (w, d, z) in old.items()}
    require(new == expected, 'Literal renumbering mismatch')
    return {'status': 'PASS_LITERAL_RENUMBERING', 'working_states': 236, 'rows': 472,
            'initial': 0, 'dispatcher': 84, 'halt': 236}


def check_stored_runtime(root, name, table_name, source_name, states, steps):
    receipt = read(root/'evidence'/(name+'.json'))
    cases = read(root/'evidence'/(name+'_cases.json'))
    sites = read(root/source_name)
    table, start = parse_table(root/table_name)
    require(receipt['status'] == 'UNIVERSAL_MATHEMATICAL_PASS', 'Missing full runtime pass')
    require(receipt['working_states'] == states and receipt['transition_rows'] == 2*states, 'Wrong runtime census')
    require(receipt['table_sha256'] == digest(root/table_name), 'Runtime table pin')
    require(receipt['sites_sha256'] == digest(root/source_name), 'Runtime source pin')
    require(receipt['engine_sha256'] == digest(root/'verification/symbolic_runtime.py'), 'Runtime engine pin')
    require(receipt['helper_sha256'] == digest(root/'verification/independent_runtime.py'), 'Runtime helper pin')
    checker = 'check_literal_runtime.py' if name == 'runtime237' else 'check_literal_runtime236.py'
    require(receipt['checker_sha256'] == digest(root/'verification'/checker), 'Runtime wrapper pin')
    keys = [(i, positive) for i, s in enumerate(sites)
            for positive in ((False, True) if s[1] == 'CD' else (False,))]
    require(len(cases) == len(keys) == receipt['cases'] == 8386, 'Incomplete case array')
    for c, key in zip(cases, keys):
        require(type(c['site_index']) is int and type(c['positive']) is bool
                and (c['site_index'], c['positive']) == key, 'Wrong guarded case order')
        require(len(c['duration']) == len(c['motion']) == 13, 'Wrong affine dimension')
        require(all(type(x) is int and x >= 0 for x in c['duration']) and c['duration'][0] >= 1, 'Nonpositive proof clock')
        require(all(type(x) is int for x in c['motion']), 'Wrong displacement type')
        require(type(c['symbolic_steps']) is int and c['symbolic_steps'] > 0, 'Wrong rule count')
        require(set(c['kinds']) <= {'literal', 'unary', 'list'}
                and sum(c['kinds'].values()) == c['symbolic_steps'], 'Wrong rule census')
    require(sum(c['symbolic_steps'] for c in cases) == steps == receipt['symbolic_steps'], 'Wrong aggregate count')
    require(min(c['duration'][0] for c in cases) == receipt['minimum_actual_steps'] == 13, 'Wrong minimum duration')
    require(receipt['directly_used_rows'] == [list(k) for k in sorted(table)], 'Missing literal row coverage')
    return {'status': 'AUDITED_STORED_COMPLETE_RUNTIME', 'name': name, 'states': states,
            'cases': len(cases), 'symbolic_steps': steps,
            'case_array_sha256': digest(root/'evidence'/(name+'_cases.json')),
            'fresh_execution_in_this_replay': False}


def safe_extract(archive, dest):
    with zipfile.ZipFile(archive) as z:
        infos = z.infolist()
        require(len(infos) <= 2000 and sum(i.file_size for i in infos) < 100_000_000, 'Unexpected dependency size')
        names = set()
        for info in infos:
            p = Path(info.filename)
            require(not p.is_absolute() and '..' not in p.parts and info.filename not in names, 'Unsafe ZIP path')
            require(not stat.S_ISLNK(info.external_attr >> 16), 'ZIP symlink')
            names.add(info.filename)
        z.extractall(dest)
    root = dest/'zfc236-research-20261019'
    require((root/'reproduce.py').is_file(), 'Wrong upstream archive root')
    return root


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full', action='store_true')
    ap.add_argument('--output-dir', type=Path, default=ROOT/'replay')
    args = ap.parse_args()
    require(sys.version_info >= (3, 10) and __debug__ and not sys.flags.optimize,
            'Python3.10+ with assertions enabled is required')
    out = args.output_dir.resolve()
    require(not out.exists() or not any(out.iterdir()), 'Choose a new or empty output directory')
    entries = check_manifest(ROOT)
    out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    result = {'status': 'RUNNING', 'full': args.full, 'manifest_files': len(entries),
              'manifest_sha256': digest(ROOT/'SHA256SUMS'), 'numbering': check_numbering(ROOT),
              'runtime_audits': [], 'jobs': []}
    specifications = [
        ('runtime237', 'baseline/zfc_composed237_old.tm', 'inputs/source.json', 237, 2261369),
        ('runtime_rotated237', 'machines/zfc_rotated237_old.tm', 'machines/sites_logical236.json', 237, 2262455),
        ('runtime236', 'machines/zfc236_old.tm', 'machines/sites_logical236.json', 236, 2267815),
    ]
    result['runtime_audits'] = [check_stored_runtime(ROOT, *spec) for spec in specifications]
    write(out/'replay.json', result)
    with tempfile.TemporaryDirectory(prefix='zfc236-supplement-') as temporary:
        work = Path(temporary)/'package'
        work.mkdir()
        for name in entries:
            target = work/name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT/name, target)
        shutil.copy2(ROOT/'SHA256SUMS', work/'SHA256SUMS')
        upstream = safe_extract(work/'upstream/ZFC236_Construction_2026-10-19.zip', Path(temporary)/'dependency')
        env = dict(os.environ)
        env['PYTHONDONTWRITEBYTECODE'] = '1'

        def job(name, argv, cwd=work):
            before = time.monotonic()
            command = [sys.executable, '-B', *map(str, argv)]
            with (out/(name+'.log')).open('w') as log:
                process = subprocess.run(command, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
            rec = {'name': name, 'returncode': process.returncode,
                   'argv': [x.replace(str(work), '$PACKAGE').replace(str(upstream), '$UPSTREAM236') for x in command],
                   'seconds': time.monotonic()-before, 'log': name+'.log'}
            print(name, 'PASS' if process.returncode == 0 else 'FAIL', round(rec['seconds'], 2), 'seconds', flush=True)
            require(process.returncode == 0, 'Failed '+name+'; see '+str(out/(name+'.log')))
            return rec

        jobs = [
            ('hilbert_certificates', ['theory/formalism_proofs.py', '--check-only', '--output', 'theory']),
            ('old_l_to_ksp', ['theory/check_l_to_ksp.py']),
            ('equational667', ['equational667/build_e667.py']),
            ('inherited_equational692', ['upstream/equational692/build704.py']),
            ('independent_fold236', ['fold236_audit/code/audit_fold236.py']),
            ('local_positive_controls', ['fold237_experiments/code/verify_controls.py']),
            ('source_experiment_audit', ['source237_experiments/audit_delivery.py']),
            ('macro_contracts', ['source237_experiments/check_macro_contracts.py']),
            ('nip_counterexample', ['source237_experiments/nip_counterexample.py']),
            ('affine_substitutions', ['source237_experiments/affine_substitutions.py']),
            ('source236_compatibility', ['source236_audit/check_compatibility.py']),
            ('independent_product', ['verification/check_source_product_invariant.py',
                '--sites', 'inputs/source.json', '--facts', 'inputs/source_abstract_facts_k16.json',
                '--summary', 'inputs/source_abstract_summary_k16.json', '--output', out/'product.json']),
            ('affine_dual237', ['verification/check_affine_dual.py', '--source', 'inputs/source.json',
                '--facts', 'evidence/affine/facts.json', '--output', out/'affine237.json']),
            ('affine_product_dual236', ['verification/check_affine_dual.py', '--source', 'machines/sites_logical236.json',
                '--facts', 'evidence/affine_product/facts.json', '--product', 'inputs/source_abstract_facts_k16.json',
                '--output', out/'affine236.json']),
        ]
        try:
            for name, argv in jobs:
                result['jobs'].append(job(name, argv))
                write(out/'replay.json', result)
            result['jobs'].append(job('incoming236_quick',
                [upstream/'reproduce.py', '--output-dir', out/'incoming236'], cwd=upstream))
            # Compare independent reconstruction of E692 with E667's pinned reference.
            require((work/'upstream/equational692/generated/E692.bits').read_bytes()
                    == (work/'equational667/reference/E692.bits').read_bytes(), 'E692 builders disagree')
            require((work/'equational667/generated/E667.bits').read_bytes()
                    == (ROOT/'equational667/generated/E667.bits').read_bytes(), 'E667 rebuilt bits differ')
            require(read(work/'theory/formalism_proof_receipt.json')['proof_nodes'] == 2015,
                    'Wrong Hilbert proof count')
            require(read(out/'affine236.json')['nonconstant_pairwise_offset_facts'] == 970,
                    'Wrong affine relation count')
            if args.full:
                fulljobs = [
                    ('fresh_runtime236', ['verification/check_literal_runtime236.py', '--table', 'machines/zfc236_old.tm',
                        '--sites', 'machines/sites_logical236.json', '--states', '236', '--output', out/'runtime236.json']),
                    ('fresh_runtime_rotated237', ['verification/check_literal_runtime236.py', '--table', 'machines/zfc_rotated237_old.tm',
                        '--sites', 'machines/sites_logical236.json', '--states', '237', '--output', out/'runtime_rotated237.json']),
                ]
                with ThreadPoolExecutor(max_workers=2) as pool:
                    futures = [pool.submit(job, name, argv) for name, argv in fulljobs]
                    for future in futures:
                        result['jobs'].append(future.result())
                for name in ('runtime236', 'runtime_rotated237'):
                    require((out/(name+'_cases.json')).read_bytes()
                            == (ROOT/'evidence'/(name+'_cases.json')).read_bytes(),
                            'Fresh case array differs: '+name)
            for name in ['theory/formalism_proof_receipt.json', 'theory/upstream_lukasiewicz_check.json',
                         'equational667/generated/verification.json', 'fold236_audit/results/independent_fold236.json',
                         'source236_audit/compatibility.json']:
                target = out/'replayed_receipts'/name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(work/name, target)
            result['status'] = 'PASS_FULL_REPLAY' if args.full else 'PASS_QUICK_REPLAY'
            result['fresh_unbounded_jobs'] = 2 if args.full else 0
            result['new_machine_discovery_claimed'] = False
            result['audited_incoming236'] = True
            result['new_equational_packet_bits'] = 667
        except Exception as error:
            result['status'] = 'FAIL'
            result['error'] = str(error)
            result['traceback'] = traceback.format_exc()
            raise
        finally:
            result['seconds'] = time.monotonic()-started
            write(out/'replay.json', result)
    print(json.dumps({k:v for k,v in result.items() if k not in ('jobs', 'runtime_audits')}, indent=2))


if __name__ == '__main__':
    main()
