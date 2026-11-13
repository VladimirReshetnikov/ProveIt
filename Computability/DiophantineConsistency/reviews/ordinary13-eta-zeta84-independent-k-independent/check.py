from pathlib import Path
from hashlib import sha256
import json,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta-zeta84-independent-k-independent');A=Path('research/ordinary13-eta-zeta84-independent-k-candidate')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
parent=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());child=json.loads((A/'candidate.json').read_text())
assert len(parent['source'])==85 and len(child['source'])==84 and len(child['witnesses'])==13
assert parent['witnesses'][9:11]==['n_eta','n_zeta'] and child['witnesses'][9:11]==['n_eta','n_k']
assert parent['fixed_numerals']==child['fixed_numerals'] and parent['domain']==child['domain']
assert [row for row in parent['source'] if 'n_zeta' in row]==[['kbase','+','n_eta','n_zeta']]
rows=[]
for row in parent['source']:
 if row==['kbase','+','n_eta','n_zeta']:continue
 rows.append([('n_k' if x=='kbase' else x) for x in row])
assert rows==child['source']
# Every child row is topological and every declared input and row is live.
known=set(child['witnesses']+child['fixed_numerals']);deps={}
for n,op,a,b in child['source']:
 assert n not in known and op in '+-*' and (isinstance(a,int) or a in known) and (isinstance(b,int) or b in known)
 known.add(n);deps[n]=[x for x in (a,b) if isinstance(x,str)]
seen=set();todo=[child['output']]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(deps.get(n,[]))
assert set(child['witnesses']+child['fixed_numerals']).issubset(seen) and all(n in seen for n in deps)
def deg(g):
 d={n:1 for n in g['witnesses']};d.update({n:0 for n in g['fixed_numerals']})
 for n,op,a,b in g['source']:
  x=d[a] if isinstance(a,str) else 0;y=d[b] if isinstance(b,str) else 0
  d[n]=x+y if op=='*' else max(x,y)
 return d[g['output']]
assert deg(child)==110
def ev(g,v,p):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],p));mod=1000000007
 for n,op,a,b in g['source']:
  x=d[a] if isinstance(a,str) else a;y=d[b] if isinstance(b,str) else b
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%mod
 return d[g['output']]
rng=random.Random(830842)
for _ in range(500):
 v=[rng.randrange(50) for _ in range(13)];p=[rng.randrange(-6,7) for _ in range(4)]
 w=v.copy();w[10]=v[9]+v[10];assert ev(parent,v,p)==ev(child,w,p)
 inverse=w.copy();inverse[10]=w[10]-w[9];assert inverse==v
# A coordinate-level boundary, not claimed to satisfy the graph zero.
v=[0]*13;v[9]=1;v[10]=0;assert v[10]<v[9]
print(json.dumps({'author_receipt_reproduces':True,'exact_all_row_substitution':True,'child_topological_and_all_inputs_live':True,'syntactic_degree_upper_bound':deg(child),'forward_inverse_controls':500,'boundary_control_is_graph_zero':False,'unrestricted_zero_equivalence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
