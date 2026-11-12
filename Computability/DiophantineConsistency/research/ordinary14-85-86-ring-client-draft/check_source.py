#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
def load(n,h):
 p=D/'research'/n/'candidate.json'; b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return json.loads(b)
old=load('ordinary14-residue-guard86','ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371')
new=load('ordinary14-qcube85-tradeoff','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7')
assert len(old['source'])==86 and len(new['source'])==85 and old['fixed_numerals']==new['fixed_numerals']
assert old['witnesses']==['Y' if x=='s' else x for x in new['witnesses']]
expected=[]
for row in old['source']:
 name=row[0]
 if name=='q3':expected.extend([row,['Y','*','q3','s']])
 elif name=='g32':expected.append(['Z',*row[1:]])
 elif name in ('g33','Z'):continue
 else:expected.append(row)
assert expected==new['source']
def calc(g,v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(8586)
for _ in range(300):
 v={x:rng.randrange(-5,6) for x in new['witnesses']+new['fixed_numerals']};a=calc(new,v)
 w={x:v[x] for x in old['witnesses'] if x!='Y'};w.update({x:v[x] for x in old['fixed_numerals']});w['Y']=a['Y'];w['r']=v['r']+v['s'];b=calc(old,w)
 assert all(a[x]==b[x] for x in ('A0','A1','Fa','g72','guard','guarded_out'))
s=(P/'RingComparison85To86.lean').read_text()
for n in ('first_cut','first_eval','main_eval','aux_eval','strong_eval','guard_eval','output_eval'):assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-residue-guard86-lean-draft','ordinary14-qcube85-lean-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'RingComparison85To86.lean',D/'research/ordinary14-residue-guard86-lean-draft/P86ResidueGraph.lean',D/'research/ordinary14-qcube85-lean-draft/P85QcubeGraph.lean']
print(json.dumps({'scope':'source/graph delta, finite signed controls and draft receipt replays; no Lean invocation','finite_controls':300,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
