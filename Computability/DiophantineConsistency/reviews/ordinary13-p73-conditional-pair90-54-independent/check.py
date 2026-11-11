#!/usr/bin/env python3
import gzip,hashlib,itertools,json,subprocess,sys
from collections import Counter
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-p73-conditional-pair90-54'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'README.md':'b7da7d8ebe67793a28b2dce4f31551e9d76c00506cda86cc8aa61391b0d3233f','check.py':'9f85dd969a7f174e8db65215eeb9b08087ff4fd5bee50bb324ad86d38328ba67','polynomial.json':'3946b8c328d692e829d1f556ffcf78cc559e885f3715ee3509f241f4e75c47c0','result.json':'355cf75a489c456d8a63645ab2f9411824e75925588e15e5d53b3f4fc756ef1f'}.items():assert sha(p/n)==h
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
sphere=base/'research/ordinary13-p73-conditional-sphere91/polynomial.json';oldpath=base/'research/ordinary13-p73-triangular91-50/p73_rewrite91_30.json';review=base/'reviews/ordinary13-p73-conditional-sphere91-independent/check.py';p72=base/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';p61=base/'con-zfc-diophantine-forms/61-congruence-carriers/positive'
for q,h in [(sphere,'3760eb7f48966ff5e550c28a28bb78d23166888679d91ee3b9928f8d79f52242'),(oldpath,'474152760b9b915e6346f0bff6b41b1db57a3634ed8dd1cf49483c2e5cc36180'),(review,'227fa4add87e478f7b3476c838f3d0cfffcbb8dfe428548a874a90d01170799c'),(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'),(p61/'ACTIVE_BINDING.json','99a0944bbf09b368b227413312bc94e9c439578cc99582de18e2ca1339ff33b9')]:assert sha(q)==h
subprocess.run([sys.executable,'-I','-S','-B',str(review)],cwd=repo,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
sg=json.loads(sphere.read_text());old=json.loads(oldpath.read_text());g=json.loads((p/'polynomial.json').read_text());assert g['witnesses']==sg['witnesses']==old['witnesses'] and g['fixed_numerals']==sg['fixed_numerals']==old['fixed_numerals'] and len(g['witnesses'])==13 and len(g['fixed_numerals'])==4
expected=[]
for r in sg['source']:
 n=r[0]
 if n in ('g90','g91','output'):continue
 elif n=='As':expected.append(['Fs','-','f2','g72'])
 elif n=='g80':expected.append(['g80','+','g78','V'])
 elif n=='g81':expected.append(['g81','*','u','g80'])
 elif n=='g88':expected.extend([['pair_product','*','g83','Fs'],['pair_residual','-','pair_product',1],['g88','*','pair_residual','pair_residual']])
 else:expected.append(r)
assert g['source']==expected and len(expected)==90 and g['output']=='g89' and Counter(r[1] for r in expected)=={'*':50,'+':24,'-':16}
have=set(g['witnesses']+g['fixed_numerals']);deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in g['fixed_numerals']})
for n,op,a,b in expected:
 assert n not in have and all(type(x)==int or x in have for x in (a,b));d=lambda x:0 if type(x)==int else deg[x]
 deg[n]=d(a)+d(b) if op=='*' else max(d(a),d(b));have.add(n)
need={g['output']}
for n,op,a,b in reversed(expected):
 if n in need:need.update((a,b))
assert all(n in need for n,_,_,_ in expected) and set(g['witnesses']+g['fixed_numerals'])<=need
assert [deg[n] for n in ('g81','g83','Fs','pair_residual','g89')]==[7,13,14,27,54]
# Independently evaluate exact integer-polynomial tails around the actual
# parent/candidate cut nodes, including both displayed ring identities.
def at(s):return {(s,):1}
def ap(a,b,sgn=1):
 d={}
 for k,v in a.items():d[k]=d.get(k,0)+v
 for k,v in b.items():d[k]=d.get(k,0)+sgn*v
 return {k:v for k,v in d.items() if v}
def mp(a,b):
 d={}
 for x,u in a.items():
  for y,v in b.items():
   k=tuple(sorted(x+y));d[k]=d.get(k,0)+u*v
 return {k:v for k,v in d.items() if v}
cuts={x:at(x) for x in ('A0','A1','Delta','f2','g72','V','u')}
def tail(graph):
 v=dict(cuts)
 def value(x):return ({():x} if x else {}) if type(x)==int else v.get(x)
 for n,op,a,b in graph['source']:
  if n in v:continue
  A,B=value(a),value(b)
  if A is not None and B is not None:v[n]=mp(A,B) if op=='*' else ap(A,B,1 if op=='+' else -1)
 return v
o,n=tail(old),tail(g);one={():1}
assert n['g81']==ap(mp(ap(cuts['V'],cuts['u']),ap(cuts['V'],cuts['u'])),mp(cuts['V'],cuts['V']),-1)
assert n['Fs']==ap(one,o['As']) and n['g83']==o['g83']
E=ap(mp(o['g83'],n['Fs']),one,-1);assert n['g89']==ap(ap(mp(cuts['A0'],cuts['A0']),mp(cuts['A1'],cuts['A1'])),mp(E,E))
# Entirely integer residue control, independent of positivity or fixed ports.
for a,f,i,v,y in itertools.product(range(4),repeat=5):
 D=(a*a+4*a+3)%4;Q=D*(f*f-1)%4;Fa=(y*y-Q*(y*y-v*v))%4;Fs=(f*f-D*i*i)%4
 assert D in (0,3) and Q in (0,1) and Fa in (0,1) and Fs in (0,1,2)
B=json.loads((p72/'ACTIVE_BINDING.json').read_text());C=json.loads((p61/'ACTIVE_BINDING.json').read_text());assert set(B['ports'])==set(C['ports'])=={'beta','K0','MC','MF'};P=1000000007;assert all(P%d for d in range(2,int(P**.5)+1));fixed={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256']==m['sha256_raw'] and C['ports'][n]['gzip_sha256']==m['sha256_gzip']
 packed=(p72/m['path']).read_bytes();assert hashlib.sha256(packed).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];v=int.from_bytes(raw,'little');assert v>0 and v.bit_length()==m['bits'];fixed[n]=v%P
# Evaluate the three complete graphs on a different weighted affine ray.
def add(a,b,s):
 z=[((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))]
 while len(z)>1 and not z[-1]:z.pop()
 return z
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%P
 while len(z)>1 and not z[-1]:z.pop()
 return z
def ray(graph):
 v={x:[i+2,i+1] for i,x in enumerate(graph['witnesses'])};v.update({k:[n] for k,n in fixed.items()})
 for n,op,a,b in graph['source']:
  A=[a%P] if type(a)==int else v[a];B=[b%P] if type(b)==int else v[b];v[n]=mul(A,B) if op=='*' else add(A,B,1 if op=='+' else -1)
 return v
v0,vs,v1=map(ray,(old,sg,g));assert v1['g83']==v0['g83']==vs['g83'] and v1['Fs']==add(v0['As'],[1],1)
assert v1['g89']==add(add(mul(v0['A0'],v0['A0']),mul(v0['A1'],v0['A1']),1),mul(add(mul(v0['g83'],v1['Fs']),[1],-1),add(mul(v0['g83'],v1['Fs']),[1],-1)),1)
assert len(v1['g89'])==55 and v1['g89'][-1]!=0
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','author_receipt_reproduced':True,'live_gates':90,'exact_degree':54,'weighted_affine_ray_leader_mod_prime':v1['g89'][-1],'prime':P,'scope':'External all-integer P73 zero equivalence; positive-input sphere link, no Lean/file binding or undominated improvement.'},indent=2))
