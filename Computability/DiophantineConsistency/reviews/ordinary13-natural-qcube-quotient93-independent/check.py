#!/usr/bin/env python3
"""Independent q³ zero-map algebra and compact-port degree review; no Lean."""
from pathlib import Path
import collections,gzip,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
p=json.loads(pin('research/ordinary13-natural-cfold-forced-x95-degree28/candidate.json','5fd11fa456867a2ed4f3b5bc58db59caab0f58736019ee864403d62124aced4e'))
c=json.loads(pin('research/ordinary13-natural-qcube-quotient93-degree56/candidate.json','346a4895448a2212ce2617ef805fd3ea164d7d8896d5bad2c210cf19cd3ef21a'))
pin('research/ordinary13-natural-qcube-quotient93-degree56/receipt.json','07440a24e5f36af72dfc90b8f8eaaa78f6f5f6280636b5026e1a1189b44ab249')
sq=pin('Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean','f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660').decode()
dr=pin('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
ref=pin('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean','4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885').decode()
assert 'theorem dvd_of_square_dvd (m z : V) (hm : 0<m) (h : m*m ∣ z*z) : m∣z' in sq
assert 'theorem nonneg_iff {x : DiffRing V} : 0 ≤ x ↔ ∃ a, x = ι a' in dr
assert 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b' in ref
assert len(p['witnesses'])==len(c['witnesses'])==13 and len(p['source'])==95 and len(c['source'])==93
assert p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals'] and p['domain']==c['domain']=='nonnegative integers'
pr={x[0]:x for x in p['source']};cr={x[0]:x for x in c['source']}
removed={'Y','M','g32','g33','g34','folded_q3Bt','Z','g38','g39','g42','A0'}
assert all(pr[n]==cr[n] for n in pr if n not in removed)
for row in [['Yquot','+','n_Y',1],['Y','*','q3','Yquot'],['new_sum','+','folded_g31','Yquot'],['new_scaled','*','qm','new_sum'],['new_diff','-','new_scaled','Bt'],['new_sq','*','new_diff','new_diff'],['new_qm2','*','qm','qm'],['new_norm','*','new_qm2','g41'],['A0','-','new_sq','new_norm']]:assert cr[row[0]]==row
for row in [['qm','*','n_J','beta'],['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['M','*','q3','qm'],['g32','*','M','folded_g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt'],['g38','*','Z','Z'],['g39','*','M','M'],['g42','*','g39','g41'],['A0','-','g38','g42']]:assert pr[row[0]]==row
for g in (p,c):
 rows={};known=set(g['witnesses']+g['fixed_numerals'])
 for name,op,a,b in g['source']:
  assert name not in known and op in '+-*' and all(type(x) is int or x in known for x in (a,b));rows[name]=(a,b);known.add(name)
 live={g['output']};todo=[g['output']]
 while todo:
  for x in rows.get(todo.pop(),()):
   if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
 assert set(rows)|set(g['witnesses'])|set(g['fixed_numerals'])<=live
 for row in [['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['sum01','+','A0sq','A1sq'],['sum23','+','Fam2','Fsm2'],['out','+','sum01','sum23']]:assert next(r for r in g['source'] if r[0]==row[0])==row
# Symbolic free-ring checks of divisibility witness, new root and A1 cancellation.
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():d[tuple(sorted(ma+mb))]+=ca*cb
 return {m:v for m,v in d.items() if v}
B,H,T,S,Bt,N=map(atom,['b','h','t','s','Bt','N']);one={():1};b2=mul(B,B);b3=mul(b2,B)
h=mul(mul(add(one,B),add(one,B)),add(one,B))
assert add(h,mul(B,add(add(b2,mul({():3},B)),{():3})),-1)==one
Z=add(add(mul(mul(H,B),T),mul(mul(H,S),B)),mul(H,Bt),-1);zn=add(mul(B,add(T,S)),Bt,-1)
assert Z==mul(H,zn)
assert add(mul(Z,Z),mul(mul(mul(H,B),mul(H,B)),N),-1)==mul(mul(H,H),add(mul(zn,zn),mul(mul(B,B),N),-1))
U,A,C,X,HH,SS=map(atom,['U','a','c','X','H','S']);b0=add(X,mul(A,C));dst=add(mul(U,b0),mul(HH,SS));delta=add(mul(A,A),HH)
lhs=add(mul(dst,dst),mul(mul(U,U),add(one,mul(delta,mul(C,C)))),-1)
inner=add(add(add(mul({():2},mul(X,mul(A,C))),mul(X,X)),one,-1),mul(HH,mul(C,C)),-1)
rhs=add(add(mul(mul(U,U),inner),mul({():2},mul(mul(mul(U,b0),HH),SS))),mul(mul(HH,HH),mul(SS,SS)))
assert lhs==rhs
# Independent upper-bound propagation with algebraic replacement for A1.
d={x:1 for x in c['witnesses']};d.update({x:0 for x in c['fixed_numerals']})
for n,op,x,y in c['source']:
 dx=0 if type(x) is int else d[x];dy=0 if type(y) is int else d[y];d[n]=dx+dy if op=='*' else max(dx,dy)
bound=max(2*d['U']+d['n_X']+d['a']+d['c'],2*d['U']+2*d['n_X'],2*d['U'],2*d['U']+d['H']+2*d['c'],d['U']+d['b0']+d['H']+d['shift'],2*d['H']+2*d['shift'])
assert bound==28 and max(d['A0'],d['Fam'],d['g72'],bound)==28
# Authenticate both port manifests and raw bytes; recompute a different-prime ray.
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=json.loads(pin('con-zfc-diophantine-forms/72-congruence-sextic/positive13/ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
fixed={}
for n,item in binding['ports'].items():
 assert b115['ports'][n]['sha256_raw']==item['sha256_raw'] and b115['ports'][n]['sha256_gzip']==item['sha256_gzip']
 raw=gzip.decompress(pin(str(root.relative_to(D)/item['path']),item['sha256_gzip']));assert len(raw)==item['raw_bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256_raw']
 fixed[n]=int.from_bytes(raw,'little')
assert set(fixed)==set(c['fixed_numerals']) and fixed['beta']>=46 and fixed['K0']>=0
prime=1000000009
def trim(x):
 while len(x)>1 and not x[-1]:x.pop()
 return x
def ap(x,y,k=1):return trim([((x[i] if i<len(x) else 0)+k*(y[i] if i<len(y) else 0))%prime for i in range(max(len(x),len(y)))])
def mp(x,y):
 d=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):d[i+j]=(d[i+j]+a*b)%prime
 return trim(d)
e={x:[0,1] for x in c['witnesses']};e.update({x:[v%prime] for x,v in fixed.items()})
for name,op,x,y in c['source']:
 x=e[x] if type(x) is str else [x%prime];y=e[y] if type(y) is str else [y%prime]
 e[name]=mp(x,y) if op=='*' else ap(x,y,-1 if op=='-' else 1)
assert len(e[c['output']])-1==56 and e[c['output']][-1]!=0
print(json.dumps({'scope':'independent exact graph/ring checks and fixed-compact-port degree; no Lean','variables':13,'natural_operations':93,'input_degree_for_authenticated_compact_ports':56,'different_ray_prime':prime,'ray_leading_coefficient':e[c['output']][-1],'nonstandard_model_divisibility_source_interfaces':True,'first_norm_scaled_by_h_squared':True,'beta_representation_required':True},sort_keys=True,indent=2))
