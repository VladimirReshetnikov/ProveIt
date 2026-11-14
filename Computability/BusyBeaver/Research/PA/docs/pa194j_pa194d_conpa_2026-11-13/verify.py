#!/usr/bin/env python3
"""Reproduce the delivered PA194J and PA194D construction certificates.

The default includes both complete independent symbolic physical checks.
--quick checks integrity, reconstruction, finite invariants, exact blank
startup, and novelty, but does not replay the universal tape contracts.
Work is performed in a temporary copy so repeated runs preserve the packet.
Python 3.10+ standard library only; no network or external checkout.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'comparison'))
from census_current_snapshot import parse, rootfree

MACHINES = [
    ('PA194J', 'construction', 'pa194j', 60062,
     '7c498ced0eb0dffed77ae2f68f4d80c98edfd8f7763ec1be68aa8cd7ea80eacd'),
    ('PA194D', 'logical_emitter', 'pa194d', 58168,
     '4226b7702de554df4b52d10239b2bd7ad79ca90bd8faf2bd256552fe0c7fe81b'),
]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def integrity():
    manifest = ROOT / 'SHA256SUMS'
    assert manifest.exists(), 'Missing SHA256SUMS.'
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = ROOT / name
        assert path.is_file() and sha(path) == expected, ('Integrity failure', name)
        count += 1
    return count

def run(script, *args):
    print('Running', script.relative_to(script.parents[1]), flush=True)
    subprocess.run([sys.executable, '-B', str(script), *map(str, args)],
                   check=True, cwd=script.parent)

def startup(folder, stem, steps):
    table = parse((folder / 'machine' / (stem + '.native.tm')).read_bytes())
    assert table is not None
    rows, controls, halt = table
    assert len(controls) == 194 and halt == 254
    ones, head, state = set(), 0, 74
    for _ in range(steps):
        assert state != halt
        write, direction, state = rows[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == 'R' else -1
    sites = json.loads((folder / 'machine' / (stem + '.sites.json')).read_text())
    path = sites[25][0]
    assert path == '1000000' and (state, head) == (84, -2)
    logical = [2] + [0] * 8
    permutation = (6, 2, 0, 4, 3, 7, 8, 5, 1)
    physical = [None] * 9
    for i, j in enumerate(permutation):
        physical[j] = logical[i]
    frame = [1] + [int(b) for b in path] + [0] * (48 - len(path)) + [1]
    for value in physical + [1] * 26:
        frame.extend([0] + [1] * (value + 1))
    expected = {head - 1 + i for i, bit in enumerate(frame) if bit}
    assert ones == expected and len(ones) == 66
    return {'steps': steps, 'state': state, 'head': head,
            'complete_tape_equal': True, 'one_cells': len(ones)}

def graph_key(path):
    table = parse(path.read_bytes())
    assert table is not None and len(table[1]) == 194
    keys = [rootfree(table, mirror, complement)[0]
            for mirror in (False, True) for complement in (False, True)]
    assert all(keys)
    return min(keys)

def main():
    assert __debug__ and not sys.flags.optimize, 'Run Python without -O.'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    args = parser.parse_args()
    started = time.monotonic()
    count = integrity()
    corpus = json.loads((ROOT / 'comparison/frontier194.json').read_text())
    old_keys = {entry['cosmetic_class_sha256'] for entry in corpus['classes']}
    assert len(old_keys) == 8
    results, new_keys = [], set()
    with tempfile.TemporaryDirectory(prefix='pa194_certificates_') as scratch:
        scratch = Path(scratch)
        for title, directory, stem, steps, dense_hash in MACHINES:
            original, working = ROOT / directory, scratch / directory
            shutil.copytree(original, working,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            run(working / 'rebuild.py')
            dense = working / 'machine' / (stem + '.tm')
            assert sha(dense) == dense_hash
            assert dense.read_bytes() == (original / 'machine' / dense.name).read_bytes()
            key = graph_key(dense)
            assert key not in old_keys and key not in new_keys
            new_keys.add(key)
            item = {'name': title, 'dense_sha256': dense_hash,
                    'cosmetic_graph_sha256': key, 'different_from_eight_old_graphs': True,
                    'startup': startup(working, stem, steps),
                    'build': json.loads((working / 'evidence/build_receipt.json').read_text())}
            if not args.quick:
                run(working / 'independent_verify.py')
                receipt = json.loads((working / 'evidence/independent_receipt.json').read_text())
                frozen = json.loads((original / 'evidence/independent_receipt.json').read_text())
                assert receipt['status'] == 'PASS'
                for field in ('contracts_sha256', 'native_sha256', 'dense_sha256',
                              'source_contracts', 'symbolic_steps', 'maximum_symbolic_steps'):
                    assert receipt[field] == frozen[field], (title, field)
                item['independent_physical_replay'] = receipt
            else:
                item['independent_physical_replay'] = 'Not run in --quick mode.'
            results.append(item)
        mask_output = scratch / 'independent_mask_replay.json'
        run(ROOT / 'comparison/independent_mask_audit.py',
            '--parent', ROOT / 'references/parent/pa194CS.instructions.json',
            '--child', scratch / 'construction/machine/pa194j.instructions.json',
            '--masks', ROOT / 'comparison/parent_masksets.json',
            '--output', mask_output)
        mask = json.loads(mask_output.read_text())
        gamma_output = scratch / 'independent_gamma_d_replay.json'
        run(ROOT / 'comparison/audit_gamma_d.py', '--output', gamma_output)
        gamma = json.loads(gamma_output.read_text())
    print(json.dumps({'status': 'PASS', 'mode': 'quick' if args.quick else 'full',
                      'integrity_files': count, 'machines': results,
                      'new_graphs_mutually_distinct': True,
                      'independent_J_invariant': mask,
                      'independent_D_emitter_and_novelty': gamma,
                      'kernel_checked': False,
                      'seconds': round(time.monotonic() - started, 3)}, indent=2))

if __name__ == '__main__':
    main()
