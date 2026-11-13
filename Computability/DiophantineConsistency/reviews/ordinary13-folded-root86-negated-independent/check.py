#!/usr/bin/env python3
"""Independent signed-fold wiring, toy algebra and inherited evidence; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2]; P=D/'research/ordinary13-folded-root86-negated'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):assert sha(p)==h,(str(p),sha(p));return p
for n,h in {'README.md':'a260f7770118fac7254b033c4e6df8e7311e192637fe2ea2760b8954e1e77c95','candidate.json':'186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166','check.py':'fb87e6799e5c981f69d8e7b04597ebf54948d712c59259619649e561647b2ba0','result.json':'2351634f5359b7c0e48306717bedb8db34f2ea2d6d5157dd24319a153250d82c'}.items():pin(P/n,h)
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-negated-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='a6952c9279ed536a956f346bc9a41b81d8e71b49244fd18b34fcf414416b3585'
def rerun(p):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180)
 assert not r.stderr and r.stdout==(p/'result.json').read_bytes(),p
rerun(P)
for n,ch,rh in [('ordinary13-folded-root86-canonical-sign-independent','55a3a8aaeef41d876039d95a9f559bc34fd06de98a584c4afc5c54e35ba89fb6','9917d21977fec836bd2bd3ae09e1fc1a2a74db2682962aad580a6ec39b1b52f2'),('ordinary13-folded-root86-toy-full-zero-independent','19b05a2069655a6eacfa91d0824afad080fe83201ba358da3e710c66b431752b','900aebfa8b65363d44e889525fc0eeb6c0b6b6c356fdec94f99db8f43260bf3a'),('ordinary13-folded-root86-probe-independent','b0896aa3f87844a7ecdee11ff2d2100f62a38982dc7094fb331762de3dc580bc','32bea007e6e01bb8f31251551a3f796b4776dd5669d23ebd29cd931d17ac8bcd')]:
 q=D/'reviews'/n;pin(q/'check.py',ch);pin(q/'result.json',rh);rerun(q)
parent=D/'research/ordinary13-four-square88-30/candidate.json';pin(parent,'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420')
p=json.loads(parent.read_text());c=json.loads((P/'candidate.json').read_text());assert p['witnesses']==c['witnesses'] and p['witnesses'][8]=='r' and p['fixed_numerals']==c['fixed_numerals']
# Delete the two old fold nodes; substitute r_old=k*Bt-sigma before g31.
expected=[]
for row in p['source']:
 name,op,a,b=row
 if name in ('folded_kBt','folded_g31'):continue
 if name=='g31':assert row==['g31','+','g30','r'];row=['g31','-','g30','r']
 if name=='g32':assert row==['g32','*','M','folded_g31'];row=['g32','*','M','g31']
 expected.append(row)
assert expected==c['source'] and len(expected)==86
assert [r[0] for r in c['source'] if 'r' in r[2:]]==['g31']
known=set(c['witnesses']+c['fixed_numerals']); used={'out'}
for name,op,a,b in c['source']:
 assert name not in known and op in '+-*' and all(isinstance(v,int) or v in known for v in (a,b));known.add(name)
for name,op,a,b in reversed(c['source']):
 if name in used:used.update(v for v in (a,b) if isinstance(v,str))
assert all(r[0] in used for r in c['source']) and set(c['witnesses']+c['fixed_numerals'])<=used
# Exact carrier algebra over a free integer polynomial ring. In the toy seed,
# Y*qm=M*s, q3*Bt=M*t and M>0, so Z=M*(ell+k-sigma+s-t).
def add(a,b,sgn=1):
 z=a.copy()
 for k,v in b.items():z[k]=z.get(k,0)+sgn*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for k,v in a.items():
  for l,w in b.items():
   key=tuple(sorted(k+l));z[key]=z.get(key,0)+v*w
 return {k:v for k,v in z.items() if v}
def v(s):return {(s,):1}
ell,k,s,t,tau,M,Bt=map(v,('ell','k','s','t','tau','M','Bt'))
base=add(add(add(ell,k),s),t,-1)
for sign in (1,-1):
 sigma=add(base,tau,-sign);z=mul(M,add(base,sigma,-1));assert z==mul(M,tau) if sign==1 else z==mul({():-1},mul(M,tau))
# Actual toy scalars: Bt=17*X+4864<18*X once X>4864, while m=X*Y²>Bt for Y>=256.
assert 17*32*9-32==4864 and 2**20>4864 and 256**2>18
# Independent nonuniform affine ray at the authenticated compact44 bytes.
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';binding=root/'ACTIVE_BINDING.json';other=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'
pin(binding,'6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf');pin(other,'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');B=json.loads(binding.read_text());C=json.loads(other.read_text());mod=1000000007;env={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];raw=gzip.decompress(pin(root/m['path'],m['sha256_gzip']).read_bytes());assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];env[n]=[int.from_bytes(raw,'little')%mod]
for i,n in enumerate(c['witnesses']):env[n]=[i+1,i+2]
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def evalpoly(op,x,y):
 if op!='*':return trim([((x[i] if i<len(x) else 0)+(1 if op=='+' else -1)*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))])
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%mod
 return trim(z)
for name,op,a,b in c['source']:env[name]=evalpoly(op,[a%mod] if isinstance(a,int) else env[a],[b%mod] if isinstance(b,int) else env[b])
assert len(env['out'])==27 and env['out'][-1]!=0
print(json.dumps({'status':'PASS_SCOPED_EXTERNAL_REVIEW','parent_gate_rows':len(p['source']),'candidate_gate_rows':len(c['source']),'all_gates_coordinates_ports_live':True,'root_branches_checked':2,'inherited_review_receipts_reproduced':3,'weighted_ray_degree':len(env['out'])-1,'weighted_ray_leader_mod_1000000007':env['out'][-1],'scope':'Conditional standard-natural parent-to-candidate existence; toy fixed-coordinate reverse guard failure; unrestricted reverse open; no Lean or file binding.'},indent=2))
