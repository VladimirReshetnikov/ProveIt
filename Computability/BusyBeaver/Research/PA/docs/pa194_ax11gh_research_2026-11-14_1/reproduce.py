#!/usr/bin/env python3
"""Recheck all four delivered machines; --full also regenerates symbolic traces.

Assertions must be enabled. This verifies finite certificates and exact table
identities. Written uniform proofs and the inherited PA calibration are the
separately identified mathematical inputs in the report.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, subprocess, sys

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'PA194AX11GH': '513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1',
    'PA194AX11GHS': '7a4738a9eedd3f53674d67568b3197d38237d11d0fc08fa3d41251a8faf8052c',
    'PA194AX11GHF': 'dba0814631acf3f2db047d729b387fd929283186503a0e251139adfaf488c687',
    'PA194AX11GHSF': 'd2d03d166c16367bf53c521ab572c24c91860e604b19cd247dd054275736b4d7',
}

def run(*args):
    subprocess.run([sys.executable, '-B', *map(str,args)], cwd=ROOT, check=True)

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Assertions are required; do not use Python -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full', action='store_true')
    args = ap.parse_args()
    run('verify.py', *(['--full'] if args.full else []))
    if args.full:
        run('acceleration/build_fast.py', '--full')
        run('acceleration/check_literal_fast.py')
    fast = load_module('fast_check', ROOT/'acceleration/build_fast.py')
    paths, results = [], []
    for family, expected_hash in EXPECTED.items():
        is_fast = family.endswith('F')
        folder = ROOT / ('acceleration/machines' if is_fast else 'machines') / family
        path = folder/'machine.tm'
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected_hash
        dense = fast.parse(path)
        assert len(dense) == 388
        assert set(q for q,b in dense) == set(range(194))
        assert all((q,b) in dense for q in range(194) for b in (0,1))
        assert set(t for w,d,t in dense.values()) - set(range(194)) == {194}
        seen, todo = {0}, [0]
        for q in todo:
            for b in (0,1):
                t = dense[q,b][2]
                if t != 194 and t not in seen:
                    seen.add(t); todo.append(t)
        assert len(seen) == 194
        rows = fast.parse(folder/'machine.native.tm')
        receipt = json.loads((folder/'receipt.json').read_text())
        assert receipt['status'] == 'PASS'
        startup = receipt['startup']
        q, head, ones = 74, 0, set()
        for _ in range(startup['steps']):
            w,d,q = rows[q,int(head in ones)]
            (ones.add if w else ones.discard)(head)
            head += 1 if d else -1
        assert (q,head,sorted(ones)) == (startup['state'],startup['head'],startup['one_cells'])
        result = dict(family=family, states=194, rows=388, dense_sha256=expected_hash,
                      startup_steps=startup['steps'], whole_blank_startup=True)
        if is_fast:
            parent = fast.parse(ROOT/'machines'/family[:-1]/'machine.native.tm')
            guard = fast.check_guards(parent)
            child = dict(parent); child.update(fast.PATCH)
            assert rows == child and guard['status'] == 'PASS'
            certdir = ROOT/'acceleration/independent_results'/family
            cert = json.loads((certdir/'receipt.json').read_text())
            assert cert['status'] == 'PASS'
            assert cert['dense_sha256'] == expected_hash
            assert cert['native_sha256'] == hashlib.sha256((folder/'machine.native.tm').read_bytes()).hexdigest()
            assert cert['contracts_sha256'] == hashlib.sha256((certdir/'contracts.json').read_bytes()).hexdigest()
            assert cert['source_outcomes'] == receipt['source_outcomes']
            result.update(local_three_to_one_cases=len(guard['local_cases']),
                          stored_independent_outcomes=cert['source_outcomes'])
        paths.append(path)
        results.append(result)
    run('verification/novelty_pair.py', *paths, '--output', 'verification/novelty_four_receipt.json')
    output = dict(status='PASS', mode='full replay' if args.full else 'certificate audit',
                  machines=results, kernel_checked=False,
                  calibration='Written proof and inherited current incoming AX11H PA calibration; see report.')
    (ROOT/'verification/reproduction_summary.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__ == '__main__':
    main()
