#!/usr/bin/env python3
"""Reproduce the finite edge-elimination experiments and optional Lean theorem.
No network, source checkout, solver, or large repository cache is used.
"""
import argparse, hashlib, json, os, subprocess
from pathlib import Path

BASE = Path(__file__).resolve().parent

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', required=True, type=Path)
    ap.add_argument('--lean', help='Optional path to Lean 4.32.0 executable')
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    exe = work / 'edge_eliminate'
    env = dict(os.environ, TMPDIR=str(work))
    subprocess.run(['g++', '-O3', '-std=c++17', str(BASE / 'edge_eliminate.cpp'), '-o', str(exe)], check=True, env=env)
    def run(table, radius, cap):
        p = subprocess.run([str(exe), str(table), str(radius), str(cap)], check=True, capture_output=True, text=True)
        return json.loads(p.stdout)
    control = run(BASE / 'positive-control.tm', 3, 8)
    assert any(h['remove'] == 1 for h in control['hits'])
    assert control == json.loads((BASE / 'positive-control.json').read_text())
    (work / 'positive-control.json').write_text(json.dumps(control, indent=2) + '\n')
    sources = json.loads((BASE / 'input-sources.json').read_text())
    reports = []
    for radius, cap, filename in [(5, 64, 'edge-elimination-results.json'), (7, 192, 'edge-elimination-radius7-results.json')]:
        expected = json.loads((BASE / filename).read_text())
        actual = []
        for source, old in zip(sources, expected, strict=True):
            table = BASE / source['filename']
            digest = hashlib.sha256(table.read_bytes()).hexdigest()
            assert digest == old['sha256']
            r = run(table, radius, cap)
            r.update(source=source['source'], sha256=digest)
            assert r == old, (source['filename'], radius)
            actual.append(r)
        (work / filename).write_text(json.dumps(actual, indent=2) + '\n')
        reports.append({'radius': radius, 'cap': cap, 'tables': len(actual),
          'removable_table_label_pairs': sum(r['tested_states'] for r in actual),
          'tested_replacement_rows': sum(r['replacement_rows_tested'] for r in actual),
          'successful_incoming_edges': sum(r['edges_with_replacements'] for r in actual),
          'full_eliminations': sum(r['full_eliminations'] for r in actual)})
    lean = {'requested': bool(args.lean)}
    if args.lean:
        p = subprocess.run([args.lean, str(BASE / 'HiddenCoordinate.lean')], capture_output=True, text=True)
        (work / 'HiddenCoordinate.check.txt').write_text(p.stdout + p.stderr)
        assert p.returncode == 0, p.stdout + p.stderr
        assert 'sorryAx' not in p.stdout + p.stderr
        lean.update(returncode=p.returncode, no_sorry_axiom=True)
    receipt = {'search_reproduction': reports, 'lean': lean}
    (work / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
