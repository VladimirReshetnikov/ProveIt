#!/usr/bin/env python3
"""Independent direct 85 main-index source/finite review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-main-index-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'MainIndex85.lean','7280db4804fd35563116b3b7ad6c9a0f5e60707996279fabd8696e475ec984fe').decode()
pin(A/'check_source.py','dd6712670cb25e8262825d0d8c5f67a915688d42e6fd944e86c7f944e7e1eb31')
receipt=pin(A/'observation.json','ee54ab99972fac6a03c929655ccb7b8f7af4d5906dec64a3ed2f075a06b5ca5b')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-main-index-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='ced3488de19e12ad9d40e15560042486b667293115e811c3751d9d9e251a956a'
pin(D/'research/ordinary14-85-main-balance-draft/MainBalance85.lean','686f10c3ff4d86433d8de75ed4897cda3ab9341824ff70213439eba3dc39d317')
pin(D/'Lean/DiophantineConsistency/ArithmeticPellClassification.lean','77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78')
pin(D/'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean','63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16')
for f in ('(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
 '(hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)',
 '(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 '∃ d m : V, m≤c beta v ∧ xcoord m (a beta v)=d ∧ ycoord m (a beta v)=c beta v',
 'H*(U beta v*v 12+X v*Y beta v*q beta v+R+1)',
 'MainBalance85Draft.norm_and_balance p beta K MC MF v',
 'ArithmeticPellClassification.solution_index (a beta v) d (c beta v) hnorm',
 'exact ⟨d,m,hm,hx,hy,hnorm,hbal⟩'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-85-main-balance-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=0
for a in range(25):
 delta=(a+1)*(a+3);assert delta==3+4*a+a*a
 d,c=1,0
 for m in range(7):
  assert m<=c and d*d==1+delta*c*c
  d,c=(a+2)*d+delta*c,d+(a+2)*c;cases+=1
print(json.dumps({'scope':'source and finite Pell controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'pell_controls':cases,
 'zero_index_included':True},sort_keys=True,indent=2))
