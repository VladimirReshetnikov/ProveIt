#!/usr/bin/env python3
"""Independent source and finite residue review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-first-index-residues-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'FirstIndexResidues.lean','4963ceffa7f08677b3ecac2bedd11673f3de0426af0883a019fdec01758ac213').decode()
pin(A/'check_source.py','24c7f741333bcb90d062b3907ba9166565fd77022a4d16c79993e786950cddcb')
receipt=pin(A/'observation.json','6b4ffd0195814b83c3d7773e251026a1ad3a43ee53529d4601cf373efae6f3e8')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-first-index-residues-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='c94bb914b69d031a951fe6cded73a6eabcdd2268aa4c925e6f4e91a8bab416bf'
pin(D/'research/ordinary14-84-first-norm-client-draft/FirstNormClient.lean','557f24cb4cc6184a3830feb01f4d70a7c228929c1f264d6dd79c07ab15b25142')
pin(D/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5')
for f in ('(hbeta : 0<beta) (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'have hQ1 : 1≤Q := pos_iff_one_le.mp hQ',
 'have he : Q-1+1=Q := tsub_add_cancel_of_le hQ1',
 'solution_residues (Q-1) tau K hdisc',
 'tau=1+2*Q*r','K=2*n+4*Q*s',
 'exact ⟨n,r,s,hnk,hx,hy,hr\',hk\'⟩'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-first-norm-client-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=0
for Q in range(1,21):
 b=2*(Q-1)+1;delta=(b+1)*(b+3);tau,y=1,0
 for n in range(8):
  K=2*y;assert n<=K and tau*tau==1+Q*(Q+1)*K*K
  assert tau>=1 and K>=2*n and (tau-1)%(2*Q)==0 and (K-2*n)%(4*Q)==0
  r=(tau-1)//(2*Q);s=(K-2*n)//(4*Q)
  assert tau==1+2*Q*r and K==2*n+4*Q*s
  tau,y=(b+2)*tau+delta*y,tau+(b+2)*y;cases+=1
print(json.dumps({'scope':'source and finite residue controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'pell_residue_cases':cases,
 'zero_index_and_Q_one_included':True},sort_keys=True,indent=2))
