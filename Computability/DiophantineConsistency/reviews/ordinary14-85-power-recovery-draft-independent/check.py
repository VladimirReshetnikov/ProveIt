#!/usr/bin/env python3
"""Independent direct 85 power source/finite review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-power-recovery-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'PowerRecovery85.lean','5bec57c11a9f364527748f75f87dfa7d256b91837c8352ab210f26c20547c129').decode()
pin(A/'check_source.py','f0c3663d7112b5888f9443e5762a1fa5780cd63bb0d6bc08ca929be03f446d85')
receipt=pin(A/'observation.json','1205280e7a2647daaf5c9d4244f840d54568e14e169a7ae42d88c917f0d8e686')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-power-recovery-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='066d42588357db167ff9e4d080a16b55c7282fba65bc8aab55e007b64a5dd1d5'
for path,h in {
 'research/ordinary14-85-growth-draft/Growth85.lean':'e664b737f02d5b5562f7b6a8b2bcc1b1e415c41cbcb71eb655e0990bc130d133',
 'research/ordinary14-85-p72-exact-indices-draft/P72ExactIndices85.lean':'a7e058541155787edeca4b42e28000799a4befad24d9a973072669320f3d6855',
 'Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean':'e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816',
 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',
 'Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean':'b7d4f6e12aba5b0b814cc7111478c89b558b2f33aafa6fef6f019b8c3dbdd74c',
}.items():pin(D/path,h)
for f in ('(hbeta46 : 46≤beta)','(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'P72ExactIndices85Draft.exact_indices','mul_left_cancel₀ (ne_of_gt hqY)',
 'have hH : H=3+qq*D','have hcross\'','projection_quotient aa R',
 'mod_cancel hHp hres','Growth85Draft.growth p beta K MC MF v',
 'rw [mod_eq_self_of_lt h3X,mod_eq_self_of_lt h3exp] at h3mod',
 'mul_left_cancel₀ (by simp : (3:V)≠0) h3mod'):
 assert f in src,f
assert 'FreeJPowerFinish.graph_power' not in src and 'fields84' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-85-growth-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cross=nondiv=0
for q in range(2,11):
 for X in range(1,15):
  if 3*X%q:continue
  for ys in range(1,4):
   Y=q**3*ys;a=Y*(X+1);H=3+4*a;D0=4*q*q*ys*(X+1)
   assert H==3+q*D0 and H*X%q==0
   for W in range(3):
    B=H*W+7;main=B+H*X//q-H*W
    assert q*(main+H*W)==q*B+H*X
    assert H*(main+H*W)+3*B==3*(main+H*W)+H*B+H*D0*X
    assert (3*B)%H==(3*main)%H
    cross+=1;nondiv+=X%q!=0
assert nondiv
intervals=0
for X in range(1,31):
 for Y in range(1,31):
  a=Y*(X+1);H=3+4*a
  for E in range(Y):
   assert 3*X<H and 3*E<H
   if (3*X)%H==(3*E)%H:assert X==E
   intervals+=1
assert (3*1)%7==(3*8)%7 and 1!=8 and 3*8>=7
print(json.dumps({'scope':'source and finite projection controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'cross_balance_cases':cross,
 'X_not_divisible_by_q':nondiv,'interval_cases':intervals,
 'missing_interval_counterexample':True},sort_keys=True,indent=2))
