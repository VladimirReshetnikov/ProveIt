#!/usr/bin/env python3
"""Independent q-cube carrier, Mersenne and degree review; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-qcube84-probe';T=D/'reviews/ordinary14-qcube85-tradeoff-independent';Q=D/'reviews/ordinary14-shifted-guard87-calibration-decoder-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','9d7bc547fb920fa4fe9b74b06f53c0f23c64a88b30515eb4b89eaa1cbcc918ac'),(P/'check.py','45f3c6263aecd90c5398e25c469547e2ecd19acc8447b85a61876e1327e639dc'),(P/'candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'),(P/'result.json','0c4964ee48a27dc990ad83fdc946922b71847c4e4f13ed9f127d6aec2e5c1390'),(T/'check.py','295cb8ac4f58cd841a4b0ae4971b168d36a45bac51978e58e4a72c898d502026'),(T/'result.json','f17544b911b3c660f48dbe630dd5e9372cee67622d4c1f7d609466bea3d3337a'),(Q/'check.py','3e3b490dee0502f592d960a7192947674bac02d70101f1e89bc982ea4cb93163'),(Q/'result.json','d58c405d5d1e0d9dd02847419d5c01b8a1f4d0a4d3b2f8e0866dc8948c01ba1e')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-qcube84-probe-math-independent/`.\nA separate independent decoder review is recorded in\n`../../reviews/ordinary14-qcube84-probe-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='acae6a2a27ef8d38c6f104fed7fd23d1ce7d18ade04fe7fe12a7691360c75312'
for p in (P,T,Q):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes(),p
parent=D/'research/ordinary14-qcube85-tradeoff/candidate.json';assert sha(parent)=='0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7';old=json.loads(parent.read_text());g=json.loads((P/'candidate.json').read_text());expected=[]
assert g['witnesses']==['w' if x=='X' else x for x in old['witnesses']] and g['fixed_numerals']==old['fixed_numerals']
for row in old['source']:
 if row[0]=='q':expected.extend([row,['X','*','q','w']])
 elif row[0] in ('g55','g56'):continue
 elif row[0]=='shift':expected.append(['shift','-','g54','r0'])
 else:expected.append(row)
assert expected==g['source'] and len(expected)==84
known=set(g['witnesses']+g['fixed_numerals']);used={'guarded_out'}
for n,op,a,b in expected:assert n not in known and all(isinstance(x,int) or x in known for x in (a,b));known.add(n)
for n,op,a,b in reversed(expected):
 if n in used:used.update(x for x in (a,b) if isinstance(x,str))
assert all(r[0] in used for r in expected) and set(g['witnesses']+g['fixed_numerals'])<=used
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bp=root/'ACTIVE_BINDING.json';other=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert sha(bp)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(other)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B=json.loads(bp.read_text());C=json.loads(other.read_text());ports={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(root/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];ports[n]=int.from_bytes(raw,'little')
beta=ports['beta'];assert beta==(1<<590069)-1 and ports['K0']>=0 and 0<ports['MC']<beta and 0<ports['MF']<2*beta
ms=D/'Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean';assert sha(ms)=='c8a132e1b28bd1cf1ed76d80e953d5568ff0c77f566ad7b2b66715c8be9641ef' and 'theorem cancel_three' in ms.read_text()
for B0 in range(4,80):
 p=2**B0-1
 for r in range(B0):assert (3*pow(2,r,p))%p!=1
# Directly check the exact main-shift reparameterization over a free ring.
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
q,Y,w,gamma=map(v,('q','Y','w','gamma'));U=mul(Y,mul(q,q));X=mul(q,w);E=mul(X,Y);assert add(mul(U,add(gamma,w,-1)),mul(E,q))==mul(U,gamma)
# Full nonuniform affine ray over actual port residues.
mod=1000000007;env={n:[i+1,i+2] for i,n in enumerate(g['witnesses'])};env.update({n:[x%mod] for n,x in ports.items()})
def trim(a):
 while len(a)>1 and not a[-1]:a.pop()
 return a
def calc(op,x,y):
 if op!='*':return trim([((x[i] if i<len(x) else 0)+(1 if op=='+' else -1)*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))])
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%mod
 return trim(z)
for n,op,a,b in expected:env[n]=calc(op,[a%mod] if isinstance(a,int) else env[a],[b%mod] if isinstance(b,int) else env[b])
assert len(env['guarded_out'])==61 and env['guarded_out'][-1]!=0
print(json.dumps({'status':'PASS_CORRECTED_STANDARD_POSITIVE_MAP','operations':84,'all_inputs_gates_ports_live':True,'mersenne_width_controls':sum(range(4,80)),'main_carrier_identity':True,'weighted_ray_degree':60,'weighted_ray_leader':env['guarded_out'][-1],'scope':'actual compact44 standard-positive existence comparison conditional on source theorem replay; no Lean or PDF binding'},indent=2))
