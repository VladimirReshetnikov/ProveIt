#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
def load(n,h):
 p=D/'research'/n/'candidate.json'; b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return json.loads(b)
old=load('ordinary14-shifted-guard87-probe','405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210')
new=load('ordinary14-residue-guard86','ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371')
assert len(old['source'])==87 and len(new['source'])==86 and old['fixed_numerals']==new['fixed_numerals']
assert old['witnesses']==['omega' if x=='h' else x for x in new['witnesses']]
expected=[]
for row in old['source']:
 if row[0]=='g25':continue
 if row[0]=='g26':expected.append(['g26','+','X','K0'])
 elif row[0]=='bt_quotient':expected.append(['bt_quotient','*','qm','h'])
 else:expected.append(row)
assert expected==new['source']
def calc(g,v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(8687)
for _ in range(300):
 v={x:rng.randrange(-5,6) for x in new['witnesses']+new['fixed_numerals']};a=calc(new,v)
 w={x:v[x] for x in old['witnesses'] if x!='omega'};w.update({x:v[x] for x in old['fixed_numerals']});w['omega']=v['h']+a['C']*v['K0'];b=calc(old,w)
 assert all(a[x]==b[x] for x in ('A0','A1','Fa','g72','guard','guarded_out'))
s=(P/'RingComparison86To87.lean').read_text()
for n in ('guard_cut','first_eval','main_eval','aux_eval','strong_eval','guard_eval','output_eval'):assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-residue-guard86-lean-draft','ordinary14-shifted-guard87-lean-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'RingComparison86To87.lean',D/'research/ordinary14-residue-guard86-lean-draft/P86ResidueGraph.lean',D/'research/ordinary14-shifted-guard87-lean-draft/P87ShiftedGuardGraph.lean']
print(json.dumps({'scope':'source/graph delta, finite signed controls and draft receipt replays; no Lean invocation','finite_controls':300,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
