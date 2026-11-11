#!/usr/bin/env python3
"""Read-only graph, exact identity, fixed-port counterexample and degree checks."""
import gzip,hashlib,itertools,json,math
from collections import Counter
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1];p72=ROOT/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,p
 return b
old=json.loads(pin(ROOT/'research/ordinary13-p73-triangular91-50/p73_rewrite91_30.json','474152760b9b915e6346f0bff6b41b1db57a3634ed8dd1cf49483c2e5cc36180'))
checkpin='70e1159e2d433676d8782c2bf4c983a9a25936ad3067f51c7796e1058f884c19';resultpin='e3ee618e93118cf4cfb6bd38cd9abdd76434fc07a000cef5db2437cfa0b233cc'
pin(ROOT/'reviews/ordinary13-p73-triangular90-50-independent/check.py',checkpin)
review=json.loads(pin(ROOT/'reviews/ordinary13-p73-triangular90-50-independent/result.json',resultpin))
assert review['status']=='PASS_SCOPED_INDEPENDENT_REVIEW' and [91,30] in review['primary_operations_degrees']
binding=json.loads(pin(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
graphsha='3760eb7f48966ff5e550c28a28bb78d23166888679d91ee3b9928f8d79f52242'
g=json.loads(pin(H/'polynomial.json',graphsha));r=old['source'];new=g['source']
assert r[82:84]==[['g83','-','y2','g82'],['Aa','-','g83',1]]
expected=[]
for row in r:
 if row[0]=='Aa':continue
 expected.append(['g88','*','g83','g83'] if row[0]=='g88' else row)
expected.append(['output','-','g91',1]);assert new==expected
assert len(new)==91 and g['witnesses']==old['witnesses'] and len(g['witnesses'])==13 and g['fixed_numerals']==old['fixed_numerals']
assert g['parent_sha256']=='474152760b9b915e6346f0bff6b41b1db57a3634ed8dd1cf49483c2e5cc36180'
ready=set(g['witnesses']+g['fixed_numerals']);byname={}
for n,op,a,b in new:
 assert n not in ready and op in ('+','-','*') and all(isinstance(x,int) or x in ready for x in (a,b))
 byname[n]=(op,a,b);ready.add(n)
need={g['output']}
for n,op,a,b in reversed(new):
 if n in need:need.update((a,b))
assert all(n in need for n,_,_,_ in new) and all(x in need for x in g['witnesses']+g['fixed_numerals'])
assert byname['g83']==('-','y2','g82') and byname['g82']==('*','Kaux','g81') and byname['Kaux']==('*','Delta','f2m')
assert byname['g81']==('-','y2','g80') and byname['g80']==('*','V','V') and byname['g78']==('+','V','u')
assert byname['g63']==('*','Delta','c2') and byname['g72']==('*','Delta','g71') and byname['As']==('-','f2m','g72')
# Exact cut polynomial evaluation of both complete tails.
def var(x):return {(x,):1}
def add(a,b):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+c
 return {m:c for m,c in z.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for m,x in a.items():
  for n,y in b.items():
   t=tuple(sorted(m+n));z[t]=z.get(t,0)+x*y
 return {m:c for m,c in z.items() if c}
one={():1};two={():2};cuts={x:var(x) for x in ['A0','A1','g83','As']}
def tail(rows,out):
 v=dict(cuts)
 for n,op,a,b in rows[83:]:
  x=({():a} if isinstance(a,int) else v[a]);y=({():b} if isinstance(b,int) else v[b]);v[n]=mul(x,y) if op=='*' else (add(x,y) if op=='+' else sub(x,y))
 return v[out]
a0=tail(r,old['output']);a1=tail(new,g['output']);assert sub(a1,a0)==mul(two,sub(cuts['g83'],one))
# Exhaustive residue controls: Delta=m²−1; f²−1 times Delta is 0 or 1 modulo 4.
for a,f,v,y in itertools.product(range(4),repeat=4):
 delta=(a*a+4*a+3)%4;q=delta*(f*f-1)%4
 assert q in (0,1)
 fa=(y*y-q*(y*y-v*v))%4
 assert fa in (0,1) and fa!=3
# Finite controls only, not the unbounded coprime-square proof in README.
for q in range(2,40):
 for v,y in itertools.product(range(-12,13),repeat=2):
  assert not ((v!=0 or y!=0) and q*v*v==(q-1)*y*y)

prime=1000000007;fixed={};portbytes={}
for n,m in binding['ports'].items():
 packed=pin(p72/m['path'],m['sha256_gzip']);raw=gzip.decompress(packed)
 assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];x=int.from_bytes(raw,'little');assert x>0 and x.bit_length()==m['bits'];portbytes[n]=x;fixed[n]=x%prime
assert portbytes['beta']==(1<<590069)-1
# Concrete positive-input counterexample to unconditional Fa != 0.
beta=portbytes['beta'];J=4;qm=J*beta;q=qm+1;G=1+qm*qm
rank=G*(q*q-1)+J*(portbytes['MC']+q*portbytes['MF']);assert rank>0
u=rank;c=3;V=c-rank-c;y=V+u;f2m=0;delta=15;I=9
fa=y*y-delta*f2m*(y*y-V*V);strong=f2m-delta*I*I
assert V==-rank and y==fa==0 and strong==-1215
rankhash=hashlib.sha256(rank.to_bytes((rank.bit_length()+7)//8,'big')).hexdigest()
# Full actual-port ray of both graphs, with all coordinates t.
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def sadd(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def smul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
def run(g):
 vals={x:[0,1] for x in g['witnesses']};vals.update({x:[v] for x,v in fixed.items()})
 def value(x):return [x%prime] if isinstance(x,int) else vals[x]
 for n,op,a,b in g['source']:vals[n]=smul(value(a),value(b)) if op=='*' else sadd(value(a),value(b),1 if op=='+' else -1)
 return vals
oldvals,newvals=run(old),run(g);assert len(newvals['output'])-1==30 and newvals['output'][-1]==103566611
assert len(oldvals['g83'])-1<=13 and len(oldvals[old['output']])-1==30
assert newvals['output']==sadd(oldvals[old['output']],smul([2],sadd(oldvals['g83'],[1],-1)),1)
print(json.dumps({'status':'PASS','graph_sha256':graphsha,'parent_sha256':g['parent_sha256'],'independent_review_checker_sha256':checkpin,'independent_review_result_sha256':resultpin,'operations':len(new),'operation_counts':dict(sorted(Counter(x[1] for x in new).items())),'live_gates':len(new),'witnesses':len(g['witnesses']),'formal_tail_identity':'new_output = old_output + 2*(Fa-1)','degree_upper':30,'upper_bound_basis':'independently reviewed parent degree 30, Fa degree <=13, exact tail identity','ray_modulus':prime,'ray_degree':len(newvals['output'])-1,'ray_leading_coefficient':newvals['output'][-1],'explicit_positive_Fa_zero':{'coordinates_except_u':1,'u_definition':'R','rank_bit_length':rank.bit_length(),'rank_unsigned_big_endian_sha256':rankhash,'Fa':0,'As':strong},'scope':'external graph/identity and finite checks; coprime-square argument in README is mathematical, not Lean'},indent=2,sort_keys=True))
