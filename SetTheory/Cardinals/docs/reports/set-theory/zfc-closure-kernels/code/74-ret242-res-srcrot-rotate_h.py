#!/usr/bin/env python3
"""Universally rotate the four shared X-to-H-plus-one source fragments."""
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('Assertions are required; do not use Python -O.')

BASE = Path(__file__).resolve().parent
OUT = BASE / 'rotate_h'
OUT.mkdir(exist_ok=True)
sites = json.loads((BASE/'sites_logical.json').read_text())
leaves = {p:(k,a) for p,k,a in sites}
nodes = {}
def read(p):
    if p in leaves:
        return leaves[p]
    t = (read(p+'0'),read(p+'1'))
    nodes[p] = t
    return t
read('')
old = ((('CD',6),(('CI',5),('CC',2))),('CI',5))
prefixes = sorted(p for p,t in nodes.items() if t==old)
assert len(prefixes)==4
newsites = []
for p,k,a in sites:
    if not any(p.startswith(q) for q in prefixes):
        newsites.append([p,k,a])
for p in prefixes:
    newsites.extend([[p+'0','CI',5],[p+'10','CD',6],[p+'11','CC',2]])
newsites.sort()
assert len(newsites)==6455
physical = [6,2,0,4,3,7,8,5,1]
phy = [[p,k,physical[a] if k in ('CI','CD') else a] for p,k,a in newsites]
for name,data in [('sites_logical.json',newsites),('sites_physical.json',phy)]:
    (OUT/name).write_text(json.dumps(data,indent=2)+'\n')
table = {}
for line in (BASE/'zfc_combined243_old.tm').read_text().splitlines():
    if not line or line.startswith('#'):
        continue
    q,b,w,d,t = line.split()
    table[int(q),int(b)] = (int(w),d,int(t))
assert table[142,0]==(0,'R',37) and table[142,1]==(1,'R',72)
table[142,0]=(0,'R',72)
table[142,1]=(1,'R',17)
(OUT/'machine_old.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items())))
(OUT/'construction.json').write_text(json.dumps({'working_states':len(table)//2,'prefixes':prefixes,'changes':[[142,0,0,'R',72],[142,1,1,'R',17]],'status':'SOURCE_ROTATION_TRUE_TABLE_RUNTIME_UNCHECKED'},indent=2)+'\n')
print(OUT)
