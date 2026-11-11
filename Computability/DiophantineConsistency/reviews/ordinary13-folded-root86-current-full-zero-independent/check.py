#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-folded-root86-current-full-zero'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'check.py':'879ee357fdf901a6234fbc62385c89d9921bcca22387e8747028aae1bf1183c9','result.json':'16253f10bacfd19c2ded758b1e8cf9d79af944b2739222a5ebbc0a8eddf30fbe'}.items():assert sha(p/n)==h
# Strip only the exact post-review link in memory; pin both the final
# README and the originally reviewed withdrawal text.
readme=(p/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='d549dd7eeb22eed5f2805fd8bfbfc4a54b20e2128fd2bbf5dba0b2ef8454057f'
tail=(b'\nIndependent review of the withdrawn attempt is recorded in\n'
      b'`../../reviews/ordinary13-folded-root86-current-full-zero-independent/`.\n')
assert readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='1673115dfa403c8f6e967468e0cf33067e6d8c2b9f14fc16bda5e82cf51e371e'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
source=base/'research/ordinary13-four-square88-30/candidate.json';survey=base/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';compact=base/'con-zfc-diophantine-forms/72-congruence-sextic/positive13/ACTIVE_BINDING.json';p115=base/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';seed=base/'reviews/current14-free-gap-current-full-zero-independent/check.py';toy=base/'reviews/ordinary13-folded-root86-toy-full-zero-independent/check.py'
for q,h in [(source,'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'),(survey,'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'),(compact,'6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'),(p115,'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'),(seed,'730bd71a266304ba52149a5ee4a0a49e54a9cd901574c1cb80e8e34cb9d2902e'),(toy,'19b05a2069655a6eacfa91d0824afad080fe83201ba358da3e710c66b431752b')]:assert sha(q)==h
for q in (seed,toy):subprocess.run([sys.executable,'-I','-S','-B',str(q)],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180)
g=json.loads(source.read_text());rows={r[0]:r for r in g['source']}
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['q3','*','q','q2'],['U','*','Y','q2'],['qF','-','q','F'],['C','-','qF','alpha'],['E','*','X','Y'],['k','+','eta','zeta'],['ell','*','E','kY'],['M','*','q3','qm'],['Bt','-','g27','g28'],['g54','*','U','gamma'],['g55','*','E','q'],['shift','-','g56','r0'],['Dstar','+','g58','g59'],['Q','*','Delta','rho'],['I','*','c2','i'],['g72','-','g71','Q'],['V','-','g76','c'],['Fa','-','y2','g82']]:assert rows[row[0]]==row
# Authenticate both distinct port bindings and verify which was used.
A=json.loads(survey.read_text())['coefficient_binding']['ports'];B=json.loads(compact.read_text())['ports'];C=json.loads(p115.read_text())['ports'];assert set(A)==set(B)==set(C)=={'beta','K0','MC','MF'}
alt={};actual={}
for n in A:
 m=A[n];packed=(survey.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(packed).hexdigest()==m['gzip_sha256'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'];alt[n]=int.from_bytes(raw,'big');assert alt[n].bit_length()==m['bits']
 m=B[n];assert C[n]['sha256_raw']==m['sha256_raw'] and C[n]['sha256_gzip']==m['sha256_gzip'];packed=(compact.parent/m['path']).read_bytes();assert hashlib.sha256(packed).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];actual[n]=int.from_bytes(raw,'little');assert actual[n].bit_length()==m['bits']
assert alt['beta']==(1<<94517)-1 and actual['beta']==(1<<590069)-1 and alt['beta']!=actual['beta']
Bbits=alt['beta'].bit_length();beta=alt['beta'];q=beta+1;K=alt['K0'];MC=alt['MC'];MF=alt['MF'];e=28633;F=(K+pow(2,e,beta))%beta;alpha=q-F-1
assert 0<F<beta and alpha>0;R=(beta*(q-F)+alpha)*(q*q-1)+MC+q*MF;assert R%4==3 and (R+1)%3==0
def ih(n):return hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'big')).hexdigest()
assert ih(F)=='411970036963b7b05d9055fb1917f3f0f636892cdf4e85b9930272e4acf56cca' and ih(R)=='3dd9c6439028ac65f4ec83ba0589e74a74221764c6d2ba342a7bd5902e9d7d3e'
d=(R+1)//3;rx=2*d;h=3*d//2;lam=d-1
assert d%4==0 and R>rx>=2*Bbits+1 and 2*h==R+1 and rx% Bbits==e and rx+lam==R and lam>=3*Bbits+2
assert rx>K.bit_length()+Bbits+10 and rx-Bbits>Bbits and ((K+pow(2,e,beta))-F)%beta==0
# rX²>2R and c=psi_A(rX)>=rX imply the selected f exceeds psi_A(R).
assert rx*rx>2*R
# Exact small countercontrol to the indexed Chebyshev claim. Use rX=8,
# R=11, as induced by d=4; all computations are exact modular arithmetic.
A0=2;rx0=8;R0=11;D=A0*A0-1
def mul(x,y):return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def power(x,n):
 y=(1,0)
 while n:
  if n&1:y=mul(y,x)
  x=mul(x,x);n//=2
 return y
D0,c=power((A0,1),rx0);f,L=power((D0,c),c);cR=power((A0,1),R0)[1];mod=f*f;S=D*L;vv=S*S%mod;P0,P1=1,(4*vv-3)%mod
for _ in range(2,(R0-1)//2+1):P0,P1=P1,((4*vv-2)*P1-P0)%mod
V=P1;assert (V+cR)%mod==0 and 0<cR-c<mod and (V+c)%mod!=0
print(json.dumps({'status':'REJECTED_FULL_ZERO_CLAIM','author_withdrawal_receipt_reproduced':True,'alternate_beta_bits':alt['beta'].bit_length(),'compact44_beta_bits':actual['beta'].bit_length(),'alternate_R_bits':R.bit_length(),'chebyshev_index_mismatch':'V congruent -psi_A(R), not -psi_A(rX); selected T is nonintegral','small_control':{'A':A0,'rX':rx0,'R':R0,'psi_rX':c,'psi_R':cR,'T_integrality_fails':True},'scope':'First/main seed and root signs conditional on inherited Pell argument; no completed alternate-port zero, compact44 zero, Lean or unrestricted nonequivalence.'},indent=2))
