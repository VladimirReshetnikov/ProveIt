#!/usr/bin/env python3
"""Actual-port partial assignment and source dependency audit; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-folded-root86-calibration-obstruction'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','6d6eb3872715131ce486a503952ec27704755bdbf9ddb1e9ba4e9e8a999464b8'),(P/'check.py','ffdaff42c0cabe48b130913f7b2dc87f03e03b994c8c5aa24084b15ba0f0c3cb'),(P/'result.json','88af643f0aacf45373e073fe820f0d993ede3fa1a99b44c40f53d3b3c5cd9936')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-calibration-obstruction-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='cc6587081492c4d07f1b0ac5f4bed98a5caa30c606025a49b57acef78ba93caf'
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(P/'result.json').read_bytes()
graph=D/'research/ordinary13-folded-root86-negated/candidate.json';assert sha(graph)=='186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166';g=json.loads(graph.read_text());rows={r[0]:r for r in g['source']}
for name,row in {'q':['q','+',1,'qm'],'C':['C','-','qF','alpha'],'G':['G','+','alpha','g44'],'Bt':['Bt','-','g27','g28'],'g31':['g31','-','g30','r'],'Z':['Z','-','g34','folded_q3Bt'],'Dstar':['Dstar','+','g58','g59'],'A0':['A0','-','g38','g42'],'A1':['A1','-','g61','g65']}.items():assert rows[name]==row
L=D/'Lean/DiophantineConsistency/Compact44';src=(L/'FreeJFirstTransport.lean').read_text();assert '(hv : ∀j,0<v j)' in src and 'M*(ell+k+v 7)' in src and 'have hBt : Bn<Bp' in src and 'have hgap : v 1+v 2<q' in src
for n in ('CompactLeafFactsLiteral','FreeJSaturationClient','FreeJPowerProjection','FreeJPowerFinish'):assert 'freej_first_factor_transport' in (L/(n+'.lean')).read_text()
window=(L/'P72Window.lean').read_text();assert '(hq : q = F + (C + α))' in window and '(hC : 1 ≤ C)' in window
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bp=p72/'ACTIVE_BINDING.json';p115=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert sha(bp)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(p115)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B=json.loads(bp.read_text());C=json.loads(p115.read_text());ports={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];ports[n]=int.from_bytes(raw,'little')
b=ports['beta'];K=ports['K0'];assert b==(1<<590069)-1 and min(ports.values())>0
s=((1-K)*pow(2,-1,b))%b or b;assert 1<=s<=b and (2*s+K-1)%b==0
# Exact polynomial identities in the single indeterminate Y, with integer coefficients.
def add(a,b,sign=1):
 z=a.copy()
 for k,v in b.items():z[k]=z.get(k,0)+sign*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for k,v in a.items():
  for l,w in b.items():z[k+l]=z.get(k+l,0)+v*w
 return {k:v for k,v in z.items() if v}
def scale(c,a):return {k:c*v for k,v in a.items() if c*v}
one={0:1};y={1:1};x=add(scale(2,y),{0:2},-1);m=mul(x,mul(y,y));p=add(scale(2,m),one);k=scale(4,p);tau=add(scale(2,mul(p,p)),one,-1);ell=mul(m,k);a=add(mul(x,y),y);A=add(a,{0:2});H=add(scale(4,a),{0:3});c=add(scale(4,mul(A,A)),one,-1);eta=add(c,mul(y,k),-1);zeta=add(k,eta,-1);d=add(scale(4,mul(mul(A,A),A)),scale(3,A),-1)
assert eta=={2:36,1:-20,0:15} and zeta=={3:16,2:-52,1:20,0:-11}
assert mul(tau,tau)==add(one,mul(mul(m,add(m,one)),mul(k,k)))
assert mul(d,d)==add(one,mul(add(mul(A,A),one,-1),mul(c,c)))
assert add(d,mul(a,c),-1)==add({0:8},mul(H,add(scale(2,a),{0:6})))
assert H==add(mul({1:8,0:36},{1:1,0:-5}),{0:183})
assert add(add(ell,k),tau,-1)==add(scale(4,m),{0:3})
print(json.dumps({'status':'PASS_ACTUAL_PORT_PARTIAL_ONLY','beta_bits':b.bit_length(),'first_and_main_bare_pell_identities':True,'source_old_coordinate_positive_hypothesis':True,'actual_scalar_congruence':True,'main_residual_excluded_by_H_divisibility':True,'scope':'actual-port partial assignment with A0=0 but A1 cannot vanish; no full zero, halt, Lean or unrestricted nonequivalence'},indent=2))
