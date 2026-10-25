#!/usr/bin/env python3
"""Read-only exact check of the 79-operation evaluator and its fixed tuple."""
from collections import Counter
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json

ROOT = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise ValueError(message)

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def main():
    old_path = ROOT/'upstream/equation_80_382_partial.json'
    old = json.loads(old_path.read_text())
    new = json.loads((ROOT/'equation79_degree382.json').read_text())
    require((ROOT/'parent80.json').read_bytes() == old_path.read_bytes(), 'Parent bytes changed')
    require(new['parent_sha256'] == hashlib.sha256(old_path.read_bytes()).hexdigest(), 'Parent binding')
    rows = {row[0]:row for row in old['source']}
    require(rows['kY'] == ['kY','*','k','Y'], 'Shared product differs')
    require(rows['V0'] == ['V0','*','D','Y'], 'Deleted register differs')
    require(rows['V0k'] == ['V0k','*','V0','k'], 'Old use differs')
    require(sum('V0' in row[2:] for row in old['source']) == 1, 'Deleted register is not private')
    expected = [(['V0k','*','D','kY'] if row[0] == 'V0k' else row)
                for row in old['source'] if row[0] != 'V0']
    require(new['source'] == expected, 'Not the claimed exact associativity rewrite')
    for key in ['domain','witnesses','fixed_numerals','coefficient_binding','output','exact_degree']:
        require(new[key] == old[key], 'Changed semantic field: '+key)
    require(len(new['source']) == new['operations'] == 79, 'Operation count')
    counts = dict(Counter(row[1] for row in new['source']))
    require(counts == new['operation_breakdown'], 'Operation breakdown')
    known = set(new['witnesses']+new['fixed_numerals'])
    dependencies = {}
    for name, op, a, b in new['source']:
        require(name not in known and op in '+-*', 'Invalid gate')
        require(all(isinstance(v,int) or v in known for v in (a,b)), 'Broken topology')
        dependencies[name] = [v for v in (a,b) if isinstance(v,str)]
        known.add(name)
    live, stack = set(), [new['output']]
    while stack:
        node = stack.pop()
        if node not in live:
            live.add(node)
            stack.extend(dependencies.get(node,[]))
    require(live == known, 'Dead gate or leaf')
    checker = load_module('retained_compact_exact_check',ROOT/'upstream/verify.py')
    parent_receipt = checker.check(old)
    leading = checker.leading_graph(new)[new['output']]
    require(leading[0] == 382 and leading[1] == checker.expected_leading(new), 'Exact degree certificate')
    recipe = load_module('retained_compact_coefficients',ROOT/'upstream/rebuild_coefficients.py')
    fixed = recipe.check_or_write(False)
    for name, meta in new['coefficient_binding']['ports'].items():
        path = ROOT/'coefficients'/meta['file']
        raw = gzip.decompress(path.read_bytes())
        require(hashlib.sha256(path.read_bytes()).hexdigest() == meta['gzip_sha256'], 'Coefficient payload changed')
        require(hashlib.sha256(raw).hexdigest() == meta['raw_sha256'], 'Coefficient integer changed')
        require(path.read_bytes() == (ROOT/'upstream/coefficients'/meta['file']).read_bytes(), 'Coefficient tuple differs from parent')
    print(json.dumps({'status':'pass','operations':79,'exact_degree':382,
        'variables':len(new['witnesses']),'domain':new['domain'],
        'identity':'(D*Y)*k = D*(k*Y)', 'operation_breakdown':counts,
        'parent_check':parent_receipt,'coefficient_reconstruction':fixed,
        'scope':'Exact unchanged polynomial, all coefficients, topology, liveness and attained degree; semantic proof inherited.'},indent=2))

if __name__ == '__main__':
    main()
