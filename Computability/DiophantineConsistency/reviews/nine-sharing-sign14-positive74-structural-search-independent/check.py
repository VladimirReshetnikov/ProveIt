#!/usr/bin/env python3
import hashlib,itertools,json,re,subprocess,sys
from collections import defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-structural-search';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();m=json.loads((p/'manifest.json').read_text())
for name,h in m['sha256'].items():assert sha(p/name)==h
assert m['source_sha256']=='cdd4117cd0b8af7eefbca2d53388068350970f78dba7e73dc9be2fe1b51f105d'
can=(p/'search_canonical.py').read_text();bas=(p/'search_basis.py').read_text();section=lambda s:s.split('def alternatives(i):',1)[1].split('\ndef replace(root,old,new):',1)[0];assert section(can)==section(bas)
# Import only the deterministic graph/rewrite definitions, not either beam.
env={};exec(compile(can[:can.index('assert len(graph(root)) == 74')],str(p/'search_canonical.py'),'exec'),env);node,alt,table,graph,rootnode=env['node'],env['alternatives'],env['N'],env['graph'],env['root'];assert len(graph(rootnode))==74
# Independently use exponent-vector polynomials for all generic local shapes.
V=['formal:'+x for x in 'abcd'];pos={x:i for i,x in enumerate(V)}
def add(a,b,k=1):
 c=defaultdict(int,a)
 for e,v in b.items():c[e]+=k*v
 return {e:v for e,v in c.items() if v}
def mul(a,b):
 c=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():c[tuple(i+j for i,j in zip(x,y))]+=u*v
 return {e:v for e,v in c.items() if v}
def poly(x):
 if isinstance(x,str):return {tuple(int(i==pos[x]) for i in range(4)):1}
 op,a,b=table[x];A,B=poly(a),poly(b);return add(A,B) if op=='add' else add(A,B,-1) if op=='sub' else mul(A,B)
cases=set()
for op,inner,side in itertools.product(('add','sub','mul'),('add','sub','mul'),range(2)):
 for a,b,c in itertools.product(V,repeat=3):
  x=node(inner,a,b);cases.add(node(op,x,c) if side==0 else node(op,c,x))
for op in ('add','sub'):
 for a,b,c,d in itertools.product(V,repeat=4):cases.add(node(op,node('mul',a,b),node('mul',c,d)))
count=0
for x in cases:
 v=poly(x)
 for y in alt(x):assert poly(y)==v;count+=1
assert len(cases)==731 and count==1056
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'exact-template-check.py')],cwd=repo,capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)==json.loads((p/'exact-template-result.json').read_text())
# Invertible integer residual change Ri ↦ Ri±Rj preserves simultaneous zero.
for a,b in itertools.product(range(-5,6),repeat=2):
 for c in (1,-1):assert ((a==0 and b==0)==(a+c*b==0 and b==0))
assert 'for i in range(5):' in bas and 'for j in range(5):' in bas and "for op in ('add','sub'):" in bas
for name,depth in (('canonical-result.txt',12),('basis-result.txt',10)):
 lines=(p/name).read_text().splitlines();assert len(lines)==depth+1 and lines[-1]=='DONE 74' and all(f'DEPTH {i} ' in lines[i] and lines[i].endswith('best 74') for i in range(depth))
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-circuit-retry01-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','generic_cases':len(cases),'rewrite_instances':count,'scope':'bounded canonical and 40 residual-basis beams, no global-minimality or Lean proof claim'},indent=2))
