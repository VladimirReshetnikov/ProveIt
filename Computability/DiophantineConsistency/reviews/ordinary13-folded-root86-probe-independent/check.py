#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from collections import Counter,defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-folded-root86-probe'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'candidate.json':'e44c211efa0f124dc00414a475b2dca0d576117aaed7f4a371aa5a687be0a540','check.py':'042e2f54ba3024da5ead6cfcd385039a712cc23aaf0faa37bd3fa00395868453','result.json':'88e753e9f07c897fb165e298cbedf3d47e6dea801ac94670e3230a19e4980c35'}.items():assert sha(p/n)==h
# Normalize only the exact post-review link/ray tail in memory; retain the
# reviewed mathematical README hash and separately pin the final bytes.
readme=(p/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='4eb2103a55577a26f4355a49f49aa9050f972ae8ed312e51a98c42dd245c829b'
tail=(b'\nIndependent scoped review is recorded in\n'
      b'`../../reviews/ordinary13-folded-root86-probe-independent/`; its distinct\n'
      b'weighted full-graph ray has degree 26 and leader 590126902 modulo 1,000,000,007.\n')
assert readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='df484e4a5f3401acf57be3bc0f6a8f023bce5f9896c3fcf98beb1d8b536bbfdd'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
parent=base/'research/ordinary13-four-square88-30/candidate.json';review=base/'reviews/ordinary13-four-square88-30-independent/check.py';p72=base/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';p115=base/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'
for q,h in [(parent,'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'),(review,'0883709a84091c0c6ff099bbf39bb9a60bf9a3f4cff7433f83a2718ade027167'),(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'),(p115,'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')]:assert sha(q)==h
subprocess.run([sys.executable,'-I','-S','-B',str(review)],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
old=json.loads(parent.read_text());g=json.loads((p/'candidate.json').read_text());src=old['source'];assert g['witnesses']==old['witnesses'] and g['fixed_numerals']==old['fixed_numerals'] and g['witnesses'][0]=='J' and len(g['witnesses'])==13 and len(g['fixed_numerals'])==4
expected=[]
for row in src:
 if row[0] in ('folded_kBt','folded_g31'):continue
 expected.append(['g32','*','M','g31'] if row[0]=='g32' else row)
assert expected==g['source'] and len(expected)==86
assert [r[0] for r in src if 'r' in r[2:]]==['g31']
# Absorbed coordinate is free of Bt, so the forward and inverse substitutions
# are triangular polynomial inverse maps with all other variables untouched.
deps={'r'}
for n,op,a,b in src:
 if a in deps or b in deps:deps.add(n)
assert 'Bt' not in deps and 'k' not in deps
have=set(g['witnesses']+g['fixed_numerals']);deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in g['fixed_numerals']})
for n,op,a,b in expected:
 assert n not in have and op in ('+','-','*') and all(type(x)==int or x in have for x in (a,b));d=lambda x:0 if type(x)==int else deg[x];deg[n]=d(a)+d(b) if op=='*' else max(d(a),d(b));have.add(n)
need={g['output']}
for n,op,a,b in reversed(expected):
 if n in need:need.update((a,b))
assert all(n in need for n,_,_,_ in expected) and set(g['witnesses']+g['fixed_numerals'])<=need
assert [deg[x] for x in ('M','ell','k','r','Bt','Y','qm','q3','U','a','c','H','shift','A0','A1','Fa','g72')]==[4,4,1,1,2,1,1,3,3,2,2,2,4,16,14,13,10]
# Evaluate actual residual subgraphs at symbolic cuts; independently prove
# the two cancellations using exact multivariate integer polynomials.
def at(s):return {(s,):1}
def add(a,b,s=1):
 d=defaultdict(int,a)
 for k,v in b.items():d[k]+=s*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():d[tuple(sorted(x+y))]+=u*v
 return {k:v for k,v in d.items() if v}
one={():1};two={():2};symbols=('M','ell','k','r','Bt','Y','qm','q3','U','a','c','H','shift','X');v={x:at(x) for x in symbols}
def ev(x):return ({():x} if x else {}) if type(x)==int else v.get(x)
for n,op,a,b in expected:
 if n in v:continue
 A,B=ev(a),ev(b)
 if A is not None and B is not None:v[n]=mul(A,B) if op=='*' else add(A,B,1 if op=='+' else -1)
M,ell,k,r,Bt,Y,qm,q3,U,a,c,H,shift,X=[v[x] for x in symbols]
delta=add(mul(M,add(k,r)),add(mul(Y,qm),mul(q3,Bt),-1));Z=add(mul(M,ell),delta)
assert v['Z']==Z
A0=add(add(mul(two,mul(mul(M,ell),delta)),mul(delta,delta)),mul(mul(M,M),add(one,mul(ell,k))),-1);assert v['A0']==A0
W=add(mul(U,X),mul(H,shift));A1=add(add(mul(two,mul(mul(mul(U,a),c),W)),mul(W,W)),mul(mul(U,U),add(one,mul(H,mul(c,c)))),-1);assert v['A1']==A1
assert max(4+1,1+1,3+2)==5 and max(8+5,2*5,2*4+max(0,4+1))==13
assert max(3+1,2+4)==6 and max(3+2+2+6,2*6,2*3+max(0,2+2*2))==13
# Independent toy evaluation: other residuals nonzero, and both possible
# absorbed-coordinate roots are negative; this is not a full zero.
inputs={x:1 for x in old['witnesses']};inputs.update({'J':1,'F':2,'alpha':1,'X':4,'Y':256,'eta':1,'zeta':1,'r':23,'beta':3,'K0':4,'MC':1,'MF':4})
def calc(graph,values):
 v=dict(values)
 for n,op,a,b in graph['source']:
  A=a if type(a)==int else v[a];B=b if type(b)==int else v[b];v[n]=A*B if op=='*' else A+B if op=='+' else A-B
 return v
w=calc(old,inputs);assert (w['q'],w['Bt'],w['k'],w['A0'],w['ell'],w['M'])==(4,12,2,0,524288,192);assert all(w[x]!=0 for x in ('A1','Fam','g72'))
rho=inputs['r']-w['k']*w['Bt'];other=-2*w['ell']-3;assert (rho,other)==(-1,-1048579)
for z in (rho,other):
 q=dict(inputs);q['r']=z;candidate=calc(g,q);assert candidate['A0']==0
q=dict(inputs);q['r']=rho;assert calc(g,q)['out']==w['out'];assert rho+w['k']*w['Bt']==inputs['r']
# Actual P72 payloads against P115 binding and a separate weighted ray.
B=json.loads((p72/'ACTIVE_BINDING.json').read_text());C=json.loads(p115.read_text());P=1000000007;assert all(P%d for d in range(2,int(P**.5)+1));fixed={};assert set(B['ports'])==set(C['ports'])==set(g['fixed_numerals'])
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];packed=(p72/m['path']).read_bytes();assert hashlib.sha256(packed).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];x=int.from_bytes(raw,'little');assert x>0 and x.bit_length()==m['bits'];fixed[n]=x%P
 if n=='beta':assert x==(1<<590069)-1
def ap(a,b,s):
 z=[((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))]
 while len(z)>1 and not z[-1]:z.pop()
 return z
def mp(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%P
 while len(z)>1 and not z[-1]:z.pop()
 return z
val={x:[i+2,i+1] for i,x in enumerate(g['witnesses'])};val.update({n:[v] for n,v in fixed.items()})
for n,op,a,b in expected:
 A=[a%P] if type(a)==int else val[a];B=[b%P] if type(b)==int else val[b];val[n]=mp(A,B) if op=='*' else ap(A,B,1 if op=='+' else -1)
assert len(val['out'])==27 and val['out'][-1]!=0
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','author_receipt_reproduced':True,'live_gates':86,'exact_degree':26,'weighted_affine_ray_leader_mod_prime':val['out'][-1],'prime':P,'toy_candidate_rho_roots':[rho,other],'scope':'All-integer polynomial automorphism and local first-factor toy control; both positive-domain zero maps and iPRA/file binding remain open.'},indent=2))
