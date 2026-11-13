#!/usr/bin/env python3
"""Guard reuse exclusions and actual-port hypotheses; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-guarded-fold89-reuse-exclusions';Q=D/'reviews/ordinary13-folded-root86-negated-positive-bt-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','dfd355b1744396a6d5a5e681ac2a3ef9e672d0fc2cae4803801a72d204d08f03'),(P/'check.py','5017e99d218f9d998d6b4818349c1044baa00d961e681acac2c793b990597bf0'),(P/'result.json','af388afd20ef236f40150361d5aac3c3bfc0fb8ea456aa91a096f969e36867d1'),(Q/'check.py','676c47df37d52784e45dc39b1a29af36f9cb7caaaaa9beb896fbc96f68f867c8'),(Q/'result.json','6067f43c969e733ca45841f4cb52b9337ef42a35f865b781cac6875abd8bb09a')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary14-guarded-fold89-reuse-exclusions-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='d7523d86f52f073eb5aa77f60e96375d60d47ff15df05c6504cddb3a6541e9db'
for p in (P,Q):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes(),p
graph=D/'research/ordinary14-guarded-fold89-26/candidate.json';assert sha(graph)=='4f0758dd44c61c72c7ac19b244336306bcb588f600debe6b4dbdb686916a6012';g=json.loads(graph.read_text());rows={r[0]:r for r in g['source']}
for n,row in {'guard':['guard','-','Bt','h'],'guard2':['guard2','*','guard','guard'],'guarded_out':['guarded_out','+','out','guard2'],'A0':['A0','-','g38','g42'],'A1':['A1','-','g61','g65'],'g31':['g31','-','g30','r']}.items():assert rows[n]==row
# Authenticate actual fixed bytes independently; beta>1 and K0<(beta+1)^2.
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bp=root/'ACTIVE_BINDING.json';other=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert sha(bp)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(other)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B=json.loads(bp.read_text());C=json.loads(other.read_text());ports={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(root/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];ports[n]=int.from_bytes(raw,'little')
beta=ports['beta'];assert beta>1 and 0<=ports['K0']<(beta+1)**2
# Independent boundary controls for Bt<2Xq^6 and k/4>2Xq^6.
checks=0
for q in range(2,30):
 b=q-1
 for X in (1,2,11):
  for K in (0,q*q-1):
   for c in range(1,b+1):
    for F in range(1,b+1):
     Bt=c*(X+K*q)-F*q
     if Bt<=0 or Bt%b:continue
     Y=q**3; k=8*X*Y*Y+4;assert Bt<q*X+q**4<2*X*q**6 and 4*Bt<k and 2*(Bt+Bt//b)<k;checks+=1
assert checks>0
print(json.dumps({'status':'PASS_FOUR_SPECIFIED_EXCLUSIONS','actual_beta_gt_one':True,'actual_K_less_than_min_q_squared':True,'independent_boundary_controls':checks,'scope':'four named existing-input guards under explicit hypotheses only; no universal guard exclusion or Lean'},indent=2))
