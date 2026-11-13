#!/usr/bin/env python3
"""Enumerate a bounded lexical import graph, without invoking Lean."""
from collections import defaultdict
from pathlib import Path
import hashlib, json, re, sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
ROOT=D/'research/ordinary14-natural-forced-gamma80-ipra-draft/Natural80Endpoint.lean'
BASE=D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json'
SLIM=D/'research/ordinary14-root74-slim-overlay/inventory.json'
N81=D/'research/ordinary14-natural81-endpoint-import-inventory/inventory.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(BASE)=='2977037ef7d1a8ebe7e9fc6a7363e9c03e887577750c70f04a573389bc839cb7'
assert sha(SLIM)=='b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e'
assert sha(N81)=='bfb90445976aed586a849295ddd5afa5c706b7da7c8b6519bb2bd022491e5f40'
base,slim,n81=(json.loads(x.read_text()) for x in (BASE,SLIM,N81))
by=defaultdict(list)
for path in (D/'research').rglob('*.lean'): by[path.stem].append(path)
assert ROOT.is_file()
graph,qualified={},{}
todo=[ROOT]
while todo:
    path=todo.pop()
    if path in graph: continue
    bare,qual=[],[]
    for line in path.read_text().splitlines():
        if not line.strip(): continue
        m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
        if not m: break
        for name in m.group(1).split():
            if '.' in name:
                target=(D/'Lean').joinpath(*name.split('.')).with_suffix('.lean')
                assert target.is_file(),(str(path),name)
                qual.append(name);qualified[name]=target
            else:
                choices=by[name]
                assert len(choices)==1,(str(path),name,[str(x) for x in choices])
                bare.append(name);todo.append(choices[0])
    graph[path]={'bare_imports':bare,'qualified_imports':qual}
order,done,active=[],set(),set()
def visit(path):
    if path in done: return
    assert path not in active,('cycle',str(path))
    active.add(path)
    for name in graph[path]['bare_imports']: visit(by[name][0])
    active.remove(path);done.add(path);order.append(path)
visit(ROOT)
def rel(path): return str(path.relative_to(D))
rows=[{'module':p.stem,'path':rel(p),'sha256':sha(p),**graph[p]} for p in order]
qrows=[{'module':n,'path':rel(p),'sha256':sha(p)} for n,p in sorted(qualified.items())]
old={r['module']:r for r in base['drafts_topological']}
new={r['module']:r for r in rows}
old81={r['module']:r for r in n81['drafts_topological']}
over={r['module']:r for r in slim['drafts_topological']}
assert len(old)==base['draft_count'] and len(over)==slim['draft_count'] and len(old81)==n81['draft_count']
assert set(old)==set(over)
common=set(new)&set(old)
source_drift=sorted(n for n in common if new[n]['sha256']!=old[n]['sha256'])
overlay_drift=sorted(n for n in common if new[n]['sha256']!=over[n]['source_sha256'])
# Compare original source bytes, not overlay bytes, because the latter deliberately rewrite imports.
qbase={r['module'] for r in base['qualified_direct_sources']}
qslim=set(slim['direct_qualified'])
q81={r['module'] for r in n81['qualified_direct_sources']}
out={
 'scope':'initial-header source inventory of bare draft closure and directly named qualified project sources only; no Lean resolution or provider closure',
 'root':rel(ROOT), 'draft_count':len(rows),'qualified_direct_count':len(qrows),
 'drafts_topological':rows, 'qualified_direct_sources':qrows,
 'root74_comparison':{'shared':len(common),'added_modules':sorted(set(new)-set(old)),
   'omitted_modules':sorted(set(old)-set(new)), 'common_source_hash_changed':source_drift,
   'added_direct_qualified':sorted(set(qualified)-qbase),'omitted_direct_qualified':sorted(qbase-set(qualified))},
 'natural81_comparison':{'shared':len(set(new)&set(old81)),'added_modules':sorted(set(new)-set(old81)),
   'omitted_modules':sorted(set(old81)-set(new)), 'common_source_hash_changed':sorted(n for n in set(new)&set(old81) if new[n]['sha256'] != old81[n]['sha256']), 'added_direct_qualified':sorted(set(qualified)-q81),
   'omitted_direct_qualified':sorted(q81-set(qualified))},
 'slim_overlay_comparison':{'overlay_draft_count':len(over),'shared_draft_modules':len(set(new)&set(over)),
   'endpoint_drafts_not_in_overlay':sorted(set(new)-set(over)),
   'overlay_drafts_not_used_by_endpoint':sorted(set(over)-set(new)),
   'common_original_source_hash_changed':overlay_drift,
   'endpoint_direct_qualified_not_in_overlay':sorted(set(qualified)-qslim),
   'overlay_direct_qualified_not_in_endpoint':sorted(qslim-set(qualified))}}
print(json.dumps(out,sort_keys=True,indent=2))
