#!/usr/bin/env python3
"""Build the coprime-fused ten-positive circuit, without changing upstream."""
import json, hashlib, collections, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
PARENT=HERE/'source/parent_equation.json'
p=json.loads(PARENT.read_text())
rows=[]
for row in p['source']:
    name,op,a,b=row
    if name=='I2':
        rows.append(['DtauI','*','Dtau','I'])
        name='DtauI2';a='DtauI';b='I'
    if name=='DpI2':
        b='DtauI2'
    if name=='HI':
        b='DtauI'
    if name=='Dtau9':
        rows.append(['pair','*','Dtau','Df'])
        continue
    if name=='fa':b='pair'
    if name=='fb':continue
    if name=='U':break
    rows.append([name,op,a,b])
rows += [
 ['omega','-','fs','fc'],
 ['diff','-','omega','fa'],
 ['diff2','*','diff','diff'],
 ['fafc','*','fa','fc'],
 ['fourfafc','*',4,'fafc'],
 ['N','-','diff2','fourfafc']]
# Exact expanded-transport rewrite, uniform in all integer inputs.
short=[]
for row in rows:
    name,op,a,b=row
    if name in {'qm1L','W','WBt','q4'}:continue
    if name=='P1':a,b='q3','qbJ'
    if name=='Hn':b='nVL'
    if name=='q3WBt':b='B'
    short.append([name,op,a,b])
    if name=='nV':short += [['LB','*','L','B'],['nVL','-','nV','LB']]
rows=short
deg={k:1 for k in p['witnesses']};deg.update({k:0 for k in p['fixed_numerals']})
def d(x):return deg[x] if isinstance(x,str) else 0
for name,op,a,b in rows:deg[name]=d(a)+d(b) if op=='*' else max(d(a),d(b))
used={'N'}
for name,op,a,b in reversed(rows):
    if name in used:
        for x in (a,b):
            if isinstance(x,str):used.add(x)
dead=[row[0] for row in rows if row[0] not in used]
assert not dead,dead
counts=dict(collections.Counter(row[1] for row in rows))
out={k:p[k] for k in ['domain','witnesses','fixed_numerals','coefficient_binding']}
out.update(name='ten_positive_coprime_fusion_expanded_transport',operations=len(rows),operation_breakdown=counts,
           exact_degree=266,syntactic_degree=deg['N'],output='N',
           parent_sha256=hashlib.sha256(PARENT.read_bytes()).hexdigest(),
           proof_status='Ordinary arithmetic reduction; exact expanded-transport rewrite of fusion98; no new internal-ZFC or Lean derivation.',
           fusion98_sha256=hashlib.sha256((HERE/'source/fusion98_equation.json').read_bytes()).hexdigest(),
           register_degrees=deg,source=rows)
serialized=json.dumps(out,indent=2)+'\n'
if '--check' in sys.argv:
    if (HERE/'equation.json').read_text()!=serialized:raise SystemExit('equation.json is not the reproducible output')
else:
    (HERE/'equation.json').write_text(serialized)
print(json.dumps({'operations':len(rows),'breakdown':counts,'syntactic_degree':deg['N'],
                  'key_degrees':{n:deg[n] for n in ['I','Dtau','Df','Q','V','L','LB','Znum','Mtot','fa','fc','fs']}}))
