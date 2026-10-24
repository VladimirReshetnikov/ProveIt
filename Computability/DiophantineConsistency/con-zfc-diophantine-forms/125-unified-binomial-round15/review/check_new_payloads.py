"""Independent read-only metric and SOS audit; imports no package programs."""
from pathlib import Path
from collections import Counter
import json, hashlib

ROOT = Path(__file__).resolve().parents[1] / 'intake'
out = {'scope': 'Exact finite payload metrics and SOS expansion, not semantic calibration', 'quartics': [], 'circuits': []}

def quartic(eq, poly):
    e = json.loads(eq.read_text()); p = json.loads(poly.read_text())
    accum = Counter()
    for row in e['residuals']:
        terms = row['terms']
        for c, mon in terms:
            for d, n in terms:
                accum[tuple(sorted(mon+n))] += c*d
    accum = {m:c for m,c in accum.items() if c}
    target = {tuple(m):c for c,m in p['terms']}
    assert len(target) == len(p['terms'])
    assert target == accum, eq
    used = set(i for m in accum for i in m)
    variables = p['variables']
    assert used == set(range(variables)), (eq, len(used), variables)
    out['quartics'].append({'path': str(eq.relative_to(ROOT)), 'domain': p.get('domain', e.get('domain', 'unrestricted integers')), 'variables': variables, 'rows': len(e['residuals']), 'terms': len(accum), 'degree': max(map(len, accum)), 'coefficient_height': max(abs(c) for c in accum.values()), 'coefficient_alphabet': sorted(set(accum.values())) if len(set(accum.values())) < 10 else None, 'polynomial_sha256': hashlib.sha256(poly.read_bytes()).hexdigest(), 'full_sos_expansion_equal': True})

for outer in ROOT.glob('ConZFC_Signed_Powers*'):
    if not outer.is_dir(): continue
    for d in outer.glob('*/*/*'):
        if d.is_dir() and (d/'equation.json').exists():
            poly = d/'polynomial.json'
            if not poly.exists(): poly = d/'expanded_polynomial.json'
            if poly.exists(): quartic(d/'equation.json', poly)
for outer in ROOT.glob('ConZFC_Synchronized*'):
    if not outer.is_dir(): continue
    for d in outer.glob('*/direct/natural*'):
        if d.is_dir(): quartic(d/'equation.json', d/'polynomial.json')
for outer in ROOT.glob('con-zfc-structural-compression*'):
    if not outer.is_dir(): continue
    for d in outer.glob('*/quartic/fused68/*'):
        if d.is_dir() and (d/'equation.json').exists(): quartic(d/'equation.json', d/'polynomial.json')
for outer in ROOT.glob('ZFC_Diophantine_Coprime*'):
    if not outer.is_dir(): continue
    for p in outer.glob('*/integer/*11*.json'):
        d = json.loads(p.read_text())
        if 'nodes' not in d: continue
        nodes = d['nodes']; live = set(); todo = [d['output']]
        while todo:
            i=todo.pop()
            if i in live: continue
            live.add(i); node=nodes[i]
            if node[0] in ('add','sub','mul'):
                assert len(node)==3 and 0 <= node[1] < i and 0 <= node[2] < i
                todo.extend(node[1:])
            else: assert node[0] in ('integer','variable','coefficient')
        counts = Counter(nodes[i][0] for i in live if nodes[i][0] in ('add','sub','mul'))
        vs = sorted(nodes[i][1] for i in live if nodes[i][0]=='variable')
        assert vs==sorted(d['variables']) and len(vs)==d['variable_count']
        assert sum(counts.values())==d['operations'] and dict(counts)==d['operation_counts']
        out['circuits'].append({'path': str(p.relative_to(ROOT)), 'domain':d['domain'], 'variables':len(vs),'operations':sum(counts.values()), 'operation_counts':dict(counts), 'claimed_exact_degree':d['exact_degree'], 'degree_not_independently_audited_here':True, 'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
dest = Path(__file__).with_name('independent_payload_metrics.json')
dest.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out, indent=2))
