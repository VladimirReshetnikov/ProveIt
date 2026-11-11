#!/usr/bin/env python3
"""Independent C-fold graph, transport and degree audit; no Lean."""
import gzip,hashlib,json,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-cfold88-28';Q=D/'reviews/ordinary14-shifted-guard87-calibration-decoder-independent';T=D/'reviews/ordinary13-folded-root86-negated-positive-bt-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','3deb526c584e0c0fa532bffcc98a651c50454871848e67529fccb55fe6de4842'),(P/'check.py','730b34a7b263df557d97a575d9e2d3b6c7189259511cfec26a93d69eb182a01b'),(P/'candidate.json','9497efb00c1059897dd6d57522267af90910224f2d37f8901b99dfc28086e333'),(P/'result.json','f05c1ffd57245deb1e5c35afe697380a3ae0139f8700baed120d3c2d2783e7d8'),(Q/'check.py','3e3b490dee0502f592d960a7192947674bac02d70101f1e89bc982ea4cb93163'),(Q/'result.json','d58c405d5d1e0d9dd02847419d5c01b8a1f4d0a4d3b2f8e0866dc8948c01ba1e'),(T/'check.py','676c47df37d52784e45dc39b1a29af36f9cb7caaaaa9beb896fbc96f68f867c8'),(T/'result.json','6067f43c969e733ca45841f4cb52b9337ef42a35f865b781cac6875abd8bb09a')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-cfold88-28-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='be5653764c82d099317adb45f88bec13862d11f1a82c244ab57ff66fdb4402c4'
for p in (P,Q,T):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes(),p
parent=D/'research/ordinary13-four-square88-30/candidate.json';assert sha(parent)=='daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420';old=json.loads(parent.read_text());g=json.loads((P/'candidate.json').read_text());assert g['witnesses']==old['witnesses'] and g['fixed_numerals']==old['fixed_numerals']
expected=[['folded_kBt','*','k','C'] if r[0]=='folded_kBt' else r for r in old['source']];assert expected==g['source'] and len(expected)==88
known=set(g['witnesses']+g['fixed_numerals']);used={'out'}
for n,op,a,b in expected:assert n not in known and all(isinstance(x,int) or x in known for x in (a,b));known.add(n)
for n,op,a,b in reversed(expected):
 if n in used:used.update(x for x in (a,b) if isinstance(x,str))
assert all(r[0] in used for r in expected) and set(g['witnesses']+g['fixed_numerals'])<=used
# Exact first-carrier coordinate substitution in a free integer ring.
def add(a,b,s=1):
 z=a.copy()
 for k,v in b.items():z[k]=z.get(k,0)+s*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for k,v in a.items():
  for l,w in b.items():
   t=tuple(sorted(k+l));z[t]=z.get(t,0)+v*w
 return {k:v for k,v in z.items() if v}
def v(n):return {(n,):1}
ell,k,r,Bt,C=map(v,('ell','k','r','Bt','C'));rho=add(add(r,mul(k,Bt),-1),mul(k,C));assert add(add(add(ell,k),r),mul(k,Bt),-1)==add(add(add(ell,k),rho),mul(k,C),-1)
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bp=root/'ACTIVE_BINDING.json';other=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert sha(bp)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(other)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B=json.loads(bp.read_text());C0=json.loads(other.read_text());ports={}
for n,m in B['ports'].items():
 assert C0['ports'][n]['sha256_raw']==m['sha256_raw'] and C0['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(root/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];ports[n]=int.from_bytes(raw,'little')
assert ports['beta']>=46 and 0<=ports['K0'] and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta']
# Independent nonuniform witness ray over authenticated port residues.
mod=1000000007;env={n:[i+1,i+2] for i,n in enumerate(g['witnesses'])};env.update({n:[x%mod] for n,x in ports.items()})
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def calc(op,x,y):
 if op!='*':return trim([((x[i] if i<len(x) else 0)+(1 if op=='+' else -1)*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))])
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%mod
 return trim(z)
for n,op,a,b in expected:env[n]=calc(op,[a%mod] if isinstance(a,int) else env[a],[b%mod] if isinstance(b,int) else env[b])
assert len(env['out'])==29 and env['out'][-1]!=0
print(json.dumps({'status':'PASS_SCOPED_C_FOLD','operations':88,'all_gates_inputs_ports_live':True,'free_ring_coordinate_identity':True,'weighted_ray_degree':28,'weighted_ray_leader':env['out'][-1],'scope':'standard-positive existence equivalence at compact44 conditional on fact-level source replay; no Lean or PDF binding'},indent=2))
