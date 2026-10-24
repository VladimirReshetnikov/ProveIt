#!/usr/bin/env python3
"""Read-only independent report metric reconstruction, importing no builder."""
import collections, hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def quartic(path):
    d=json.loads((ROOT/path/'equation.json').read_text())
    p=collections.defaultdict(int)
    for row in d['residuals']:
        for a,am in row['terms']:
            for b,bm in row['terms']:
                p[tuple(sorted(am+bm))]+=a*b
    p={m:c for m,c in p.items() if c}
    stored=json.loads((ROOT/path/'expanded_polynomial.json').read_text())
    q={tuple(m):c for c,m in stored['terms']}
    if len(q)!=len(stored['terms']) or p!=q:
        raise ValueError('Coefficient mismatch '+path)
    live={v for m in p for v in m}
    if live != set(range(len(d['variables']))): raise ValueError('Variable liveness')
    return dict(domain=d['domain'], variables=len(d['variables']),rows=len(d['residuals']),terms=len(p),degree=max(map(len,p)),height=max(map(abs,p.values())),complete_expansion_agrees=True)

def dag(path):
    d=json.loads((ROOT/path).read_text())
    nodes=d['nodes']; seen=set()
    def visit(n):
        if n in seen:return
        seen.add(n)
        nd=nodes[n]
        if nd[0] in {'add','sub','mul'}:
            if len(nd)!=3 or not all(isinstance(x,int) and 0<=x<n for x in nd[1:]):raise ValueError('Topology')
            visit(nd[1]);visit(nd[2])
    visit(d['output'])
    ops=collections.Counter(nodes[i][0] for i in seen if nodes[i][0] in {'add','sub','mul'})
    if len(seen)!=len(nodes):raise ValueError('Nonlive node')
    if sum(ops.values())!=d['operations'] or dict(ops)!=d['operation_counts']:raise ValueError('Op mismatch')
    variables=[nd[1] for nd in nodes if nd[0]=='variable']
    if variables!=d['variables'] or len(variables)!=11:raise ValueError('Variables')
    return dict(domain=d['domain'],variables=variables,operations=sum(ops.values()),counts=dict(ops),all_nodes_live=True,sha256=hashlib.sha256((ROOT/path).read_bytes()).hexdigest())

out={'quartics':{p:quartic(p) for p in ['direct/integer442','architecture/unified_derived_cantor/natural']},'norm_graphs':{p:dag(p) for p in ['norm/integral_centered_paired.json','norm/integral_direct_paired.json','norm_weak/weak_integral_centered_paired.json','norm_weak/weak_integral_direct_paired.json']}}
print(json.dumps(out,indent=2))
(ROOT/'report_audit/METRICS.json').write_text(json.dumps(out,indent=2)+'\n')
