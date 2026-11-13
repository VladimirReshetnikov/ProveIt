#!/usr/bin/env python3
"""Independent 85 first-index source and finite review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-first-index-residues-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'FirstIndexResidues85.lean','0f3f24248f51dbac48bcb2b3dcfd0bac2468b1a984fa326a4cd85b0722c6a963').decode()
pin(A/'check_source.py','8ac104e24bbad706162e40ab3fc6fd59bd094d306e74b72d1d91add84556ee9a')
receipt=pin(A/'observation.json','e7bc65ce93e672565c611829f6bc7187d675367d976150245019ab0002a9ad33')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-first-index-residues-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='142d0b31628751567b62953fd771555419d755db7f3d112ccc2e7d25f8121a68'
pin(D/'research/ordinary14-85-direct-norms-draft/DirectNorms85.lean','2b07f618dc5e76fd6e274596d4425c5c76dbd60919014febb024a9a99265c622')
pin(D/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5')
for f in ('(hbeta : 0<beta) (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)',
 '(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'let Q := (X v*Y beta v)*Y beta v','have hX : 0<X v := hw',
 'have he : Q-1+1=Q := tsub_add_cancel_of_le hQ1',
 'solution_residues (Q-1) tau K hdisc','tau=1+2*Q*r','K=2*n+4*Q*s'):
 assert f in src,f
assert 'fields84' not in src and 'FreeJ.zero' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-85-direct-norms-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=nondiv=0
for q in range(2,8):
 for X in range(1,6):
  for s0 in (1,2):
   Y=q**3*s0;Q=X*Y*Y;b=2*(Q-1)+1;delta=(b+1)*(b+3);tau,y=1,0
   for n in range(5):
    k=2*y
    assert n<=k and tau*tau==1+Q*(Q+1)*k*k
    assert tau>=1 and k>=2*n and (tau-1)%(2*Q)==0 and (k-2*n)%(4*Q)==0
    r=(tau-1)//(2*Q);s=(k-2*n)//(4*Q)
    assert tau==1+2*Q*r and k==2*n+4*Q*s
    tau,y=(b+2)*tau+delta*y,tau+(b+2)*y
    cases+=1;nondiv+=X%q!=0
assert nondiv
print(json.dumps({'scope':'source and finite Pell residues only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'pell_cases':cases,
 'X_not_divisible_by_q':nondiv},sort_keys=True,indent=2))
