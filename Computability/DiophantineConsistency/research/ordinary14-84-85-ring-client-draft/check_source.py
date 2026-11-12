#!/usr/bin/env python3
"""No-Lean source inventory, exact carrier cut and signed graph controls."""
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
oldpath=D/'research/ordinary14-qcube85-tradeoff/candidate.json';newpath=D/'research/ordinary14-qcube84-probe/candidate.json'
def load(p,h):
 x=p.read_bytes();assert hashlib.sha256(x).hexdigest()==h;return json.loads(x)
old=load(oldpath,'0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7');new=load(newpath,'cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61')
assert len(old['source'])==85 and len(new['source'])==84 and old['fixed_numerals']==new['fixed_numerals']
assert old['witnesses']==['X' if x=='w' else x for x in new['witnesses']]
expected=[]
for row in old['source']:
 if row[0]=='q':expected.extend([row,['X','*','q','w']])
 elif row[0] in ('g55','g56'):continue
 elif row[0]=='shift':expected.append(['shift','-','g54','r0'])
 else:expected.append(row)
assert expected==new['source']
def add(a,b,sign=1):
 z=a.copy()
 for m,x in b.items():z[m]=z.get(m,0)+sign*x
 return {m:x for m,x in z.items() if x}
def mul(a,b):
 z={}
 for m,x in a.items():
  for n,y in b.items():
   k=tuple(sorted(m+n));z[k]=z.get(k,0)+x*y
 return {k:x for k,x in z.items() if x}
def v(n):return {(n,):1}
q,q3,s,w,g=map(v,('q','q3','s','w','g'));U=mul(mul(q3,s),mul(q,q));E=mul(mul(q,w),mul(q3,s))
assert add(mul(U,add(g,w,-1)),mul(E,q))==mul(U,g)
def calc(g,v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(8485)
for _ in range(200):
 vals={n:rng.randrange(-4,5) for n in new['witnesses']+new['fixed_numerals']};n=calc(new,vals)
 o={x:vals[x] for x in old['witnesses'] if x!='X'};o.update({x:vals[x] for x in old['fixed_numerals']});o['X']=n['X'];o['gamma']=vals['gamma']-vals['w'];z=calc(old,o)
 assert all(n[x]==z[x] for x in ('A0','A1','Fa','g72','guard','guarded_out'))
source=H/'RingComparison.lean';s0=source.read_text()
for n in ('factor_main','first_eval','main_eval','aux_eval','strong_eval','guard_eval','output_eval'):
 assert re.search(r'\btheorem\s+'+n+r'\b',s0)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s0))
for d in ('ordinary14-qcube84-lean-draft','ordinary14-qcube85-lean-draft'):
 p=D/'research'/d;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[source,D/'research/ordinary14-qcube84-lean-draft/P84QcubeGraph.lean',D/'research/ordinary14-qcube85-lean-draft/P85QcubeGraph.lean']
print(json.dumps({'scope':'source inventory, exact carrier cut and finite signed controls only; no Lean invocation','signed_controls':200,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
