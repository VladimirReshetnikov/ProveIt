#!/usr/bin/env python3
"""Independent natural-rank source/finite review; no Lean invocation."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-natural-rank-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'NaturalRank.lean','d9f4c4911951201d5b3b0ed72c02bfc8e5d8b56dcd7dafc378e5273d0686a350').decode()
pin(A/'check_source.py','c18a63f27d0a624f4e8c79bb039715282e9303428ef8d025fc7be51ee1606c72')
receipt=pin(A/'observation.json','f6c5c5bbfe066b5dba407c9815eb1847931517168fbb1bfff9c5c0f08537f004')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-natural-rank-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='5d650f6a6fcf102ba512e37a7b7fb0fb26651b19caf0329925653fa484adfb0e'
for path,h in {
 'research/ordinary14-84-guard-gap-draft/GuardGap.lean':'e87aac162031101468b263a119fc5a88073b4cbdbf2bd3fb12608b626709e9e5',
 'research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean':'c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e',
 'Lean/DiophantineConsistency/Compact44/P72Root.lean':'066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091',
}.items():pin(D/path,h)
for f in ('(v 2+(q-v 1)*(v 0*beta))*(q*q-1)+v 0*(MC+MF*q)',
 '(hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)',
 '(hF : v 1≤AuxGraphNormClientDraft.q beta v)',
 '(hq2 : 1≤AuxGraphNormClientDraft.q beta v*AuxGraphNormClientDraft.q beta v)',
 'P72Root.ι_tsub hF','P72Root.ι_tsub hq2',
 '(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'gap_of_84_zero p beta K v hbeta hK hFpos hw hz'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-guard-gap-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=boundary=0
for J,beta,alpha,MC,MF in itertools.product(range(4),range(4),range(4),range(3),range(3)):
 q=1+J*beta
 for F in range(q+1):
  rank_n=(alpha+max(q-F,0)*J*beta)*max(q*q-1,0)+J*(MC+MF*q)
  rank_signed=(alpha+(q-F)*J*beta)*(q*q-1)+J*(MC+MF*q)
  assert q*q>=1 and rank_n==rank_signed
  cases+=1;boundary+=F==q
assert boundary
q=2;F=3;J=beta=1;alpha=MC=MF=0
assert (alpha+max(q-F,0)*J*beta)*max(q*q-1,0)!= (alpha+(q-F)*J*beta)*(q*q-1)
print(json.dumps({'scope':'source and finite rank controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'rank_cases':cases,
 'F_eq_q_boundary':boundary,'F_exceeds_q_counterexample':True},sort_keys=True,indent=2))
