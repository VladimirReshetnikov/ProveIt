#!/usr/bin/env python3
from pathlib import Path
from collections import Counter
from functools import lru_cache
import hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-75-74-ring-client-draft';G=D/'research/ordinary14-unit75-guard74-lean-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'ad077192d1a307264b54e924f4e3998d9248b9e14f1b10f4de92d411b5b313da',A/'Ring75To74.lean':'50f5b856f5c9fc379c035d91dc19e4b97c9234feed3918785f66900d69a049b6',A/'check_source.py':'1a00a509248b50237930bfe64a9337c6c8770c8e993daae5e414570bb4bdfe76',A/'observation.json':'740b5b2984dccf24d3f16fb8ac2230b57ae9d3a0f95c59279ece16cd46520684',G/'P75NegativePell.lean':'1ef538a3af4f2c1bb162fe335683d6522a6744831168c94b79132646f3496dbe',G/'P74PositiveGuard.lean':'5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b',G/'make_graph.py':'c95e5102f34f79883f789e58230e2f0cfb721b2a8911091e3e3441e0567b52bf',G/'observation.json':'083fa7cd3a01541f7f5ce84bc29f1c4eef308ae431fb3625fd014ac5c0d61f2e',D/'research/ordinary14-negative-pell75/candidate.json':'89a9a0217d28d655fbf2592d995f4d766175a45560fa4d33b251dd3711e5b1c1',D/'research/ordinary14-positive-guard74/candidate.json':'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'}
tail=b'\nIndependent source review: [75 to 74 ring client](../../reviews/ordinary14-75-74-ring-client-independent/README.md).\n'
readme=(A/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='fe36560f581dbc69562172a7bbe674c71ac402c8f0b0961e18cade2882ad6ab9'
assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()==pins[A/'README.md']
for p,h in pins.items():
 if p!=A/'README.md':assert sha(p)==h,(str(p),sha(p))
source=(A/'Ring75To74.lean').read_text()
for x in ('Function.update v 13 (v 13+1)','theorem guard_cut','theorem common_fields','theorem restricted_eval','theorem guard_eval','theorem output_eval','C*(X+K)+(1+b-F)-b*(h+1)=1+(C*(X+K)-F-b*h)'):
 assert x in source,x
old=json.loads((D/'research/ordinary14-negative-pell75/candidate.json').read_bytes());new=json.loads((D/'research/ordinary14-positive-guard74/candidate.json').read_bytes())
assert old['witnesses']==new['witnesses'] and old['fixed_numerals']==new['fixed_numerals']
def graph(g):return {row[0]:tuple(row[1:]) for row in g['source']}
o=graph(old);n=graph(new)
def expr(rows,entry):
 @lru_cache(None)
 def rec(x):
  if not isinstance(x,str):return ('const',x)
  if x not in rows:return ('leaf',x)
  op,a,b=rows[x];return (op,rec(a),rec(b))
 return rec(entry)
def leaves(t):
 if t[0]=='leaf':return {t[1]}
 if t[0]=='const':return set()
 return leaves(t[1])|leaves(t[2])
for name in ('F0','F1','Fa','Fs'):
 t=expr(o,name);assert t==expr(n,name) and 'h' not in leaves(t),name
for graphrows,guard in ((o,'Fg'),(n,'guard')):
 assert graphrows['P01']==('*','F0','F1')
 assert graphrows['P012']==('*','P01','Fa')
 assert graphrows['P0123']==('*','P012','Fs')
 assert graphrows['P01234']==('*','P0123',guard)
 assert graphrows['out']==('-','P01234',1)
for rows in (o,n):
 assert rows['qm']==('*','J','beta') and rows['q']==('+',1,'qm')
 assert rows['qF']==('-','q','F') and rows['C']==('-','qF','alpha')
 assert rows['X']==('*','q','w') and rows['g26']==('+','X','K0')
 assert rows['g27']==('*','C','g26') and rows['bt_quotient']==('*','qm','h')
for name in ('qm','qF','C','X','g26','g27'):
 assert expr(o,name)==expr(n,name) and 'h' not in leaves(expr(o,name))
assert o['guard_base']==('-','g27','F') and o['Fg']==('+',1,'guard')
assert n['guard_base']==('+','g27','qF') and n['guard']==('-','guard_base','bt_quotient')
# Free commutative Z-polynomial identity at the exact C,X,K,F,b,h cut.
def add(a,b):
 c=Counter(a);c.update(b);return {k:v for k,v in c.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 c=Counter()
 for x,xc in a.items():
  for y,yc in b.items():c[tuple(sorted(x+y))]+=xc*yc
 return {k:v for k,v in c.items() if v}
def sub(a,b):return add(a,neg(b))
const={():1};C,X,K,F,b,h=({(z,):1} for z in ['C','X','K','F','b','h'])
oldguard=add(const,sub(sub(mul(C,add(X,K)),F),mul(b,h)))
newguard=sub(add(mul(C,add(X,K)),sub(add(const,b),F)),mul(b,add(h,const)))
assert oldguard==newguard
# Independent ring evaluations in composite and prime residue rings.
def evalgraph(g,v,m):
 v=dict(v)
 for name,op,a,b in g['source']:
  x=v[a] if isinstance(a,str) else a;y=v[b] if isinstance(b,str) else b
  v[name]=({'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]())%m
 return v
rng=random.Random(73491);count=0
for m in (4,12,17):
 for _ in range(200):
  v={k:rng.randrange(m) for k in old['witnesses']+old['fixed_numerals']};w=dict(v);w['h']=(w['h']+1)%m
  a=evalgraph(old,v,m);b=evalgraph(new,w,m)
  assert all(a[x]==b[x] for x in ('F0','F1','Fa','Fs','out'))
  assert a['Fg']==b['guard'];count+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert rr.stdout==(A/'observation.json').read_bytes() and not rr.stderr
print(json.dumps({'scope':'independent graph DAG, free-ring guard identity and finite ring controls; no Lean elaboration or positive-model claim','restricted_fields_identical_and_h_free':True,'guard_free_ring_monomials':len(oldguard),'output_shapes_match':True,'finite_ring_assignments':count,'author_receipt_replayed':True,'reviewed_author_readme_sha256':pins[A/'README.md']},sort_keys=True,indent=2))
