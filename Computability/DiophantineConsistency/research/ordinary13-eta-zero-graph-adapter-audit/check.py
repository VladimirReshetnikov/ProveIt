#!/usr/bin/env python3
"""Structural eta-unshift prototype; never proves zero equivalence or invokes Lean."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-natural-forced-w86/candidate.json':'75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50',
'research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src':'a5aac5250b0b4c05fa765ed1013e5287706f038ea60e5083d9c4cba4025e0e74',
'Lean/DiophantineConsistency/Compact44/P72Early.lean':'',
'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean':'29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd',
'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794'}
# An explicit P72Early hash is embedded below by the author after source inspection.
pins['Lean/DiophantineConsistency/Compact44/P72Early.lean']='3a1ee2f82ba4d0a1c22f402cebb2a9c031e37a442842645fe234e27c0ffca1d5'
raw={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;raw[p]=b
old=json.loads(raw['research/ordinary13-natural-forced-w86/candidate.json'])
assert ['eta','+','n_eta',1] in old['source']
rows=[]
for row in old['source']:
 if row==['eta','+','n_eta',1]:continue
 rows.append([('n_eta' if x=='eta' else x) for x in row])
new={'name':'eta-natural structural prototype; no zero equivalence or reduction claim',
'domain':old['domain'],'witnesses':old['witnesses'],'fixed_numerals':old['fixed_numerals'],
'source':rows,'output':old['output'],'parent_sha256':pins['research/ordinary13-natural-forced-w86/candidate.json'],
'proof_status':'structural substitution only; eta-zero exclusion and zero maps unproved'}
b=(json.dumps(new,indent=2,ensure_ascii=False)+'\n').encode();path=here/'prototype.json'
if '--write' in sys.argv:path.write_bytes(b)
else:assert path.read_bytes()==b
r={row[0]:row for row in rows}
expected=[['kbase','+','n_eta','n_zeta'],['k','+','kbase',1],['c','+','n_eta','kY'],['shift','-','g54','r0'],['A0','-','g38','g42'],['A1','-','g61','g65'],['g72','-','g71','Q'],['Fa','-','y2','g82'],['out','-','P0123',1]]
for row in expected:assert r[row[0]]==row,row
available=set(new['witnesses']+new['fixed_numerals'])
for name,op,a,c in rows:
 assert name not in available and op in '+-*'
 assert isinstance(a,int) or a in available
 assert isinstance(c,int) or c in available
 available.add(name)
assert new['output'] in available
P=1000000007
def evalgraph(g,vals):
 e={k:v%P for k,v in vals.items()}
 for n,op,a,c in g['source']:
  x=a%P if isinstance(a,int) else e[a];y=c%P if isinstance(c,int) else e[c]
  e[n]=({'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]())%P
 return e[g['output']]
rng=random.Random(429)
for i in range(100):
 v={x:rng.randrange(-20,21) for x in new['witnesses']+new['fixed_numerals']}
 w=dict(v);w['n_eta']=v['n_eta']+1
 assert evalgraph(old,v)==evalgraph(new,w)
print(json.dumps({'source_pins':pins,'prototype_sha256':hashlib.sha256(b).hexdigest(),'rows_topological':True,'original_to_prototype_shift_controls':100,'scope':'exact graph substitution plus bounded controls; no eta-zero exclusion, reverse zero map, Lean, or endpoint','lean_executed':False},sort_keys=True,indent=2))
