#!/usr/bin/env python3
"""Independent direct 85 growth source/finite review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-growth-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'Growth85.lean','e664b737f02d5b5562f7b6a8b2bcc1b1e415c41cbcb71eb655e0990bc130d133').decode()
pin(A/'check_source.py','9ca7e40ded384e6777f8bb5f2072f44fcdefe4ebbc2827fb49cbc5b621728c3c')
receipt=pin(A/'observation.json','1e993716197037b7db16b2637c9ae55400e978a8fcec4adfecd37b675bfbbf05')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-growth-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='de1a42962f30eb35d39a9eb2d5872e72dc90081995ab31df4b18fda12bcd7a07'
pin(D/'research/ordinary14-85-divides-3x-draft/Divides3X85.lean','bd13831f6d3aa49a336cd90413a8d64ac2ea473aa4c45e71d405925760ebb5c7')
pin(D/'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean','636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390')
pin(D/'Lean/DiophantineConsistency/Compact44/FreeJPowerGrowth.lean','bb7a5f880d4aa1a4543bab00dcb32b8a0db12e9c75caca862d7c9a397103a4aa')
for f in ('(hbeta46 : 46≤beta)','(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'Divides3X85Draft.divides_three_X p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'Arithmetic.le_of_dvd','P72ExactIndices85Draft.exact_indices',
 'have hrplus : r+1=n := tsub_add_cancel_of_le hn1',
 'have hR : R=2*r+1','have hc : cc=ycoord (2*r+1) (yy*(xx+1))',
 'have hk : kk=2*ycoord (r+1) (2*(xx*yy*yy-1)+1)',
 'power_bound xx yy r kk cc (v 9) (v 10) hX (pos_iff_one_le.mp hY) hr2',
 'Exp.exp (naturalRank beta MC MF v)<Y beta v'):
 assert f in src,f
assert 'FreeJPowerGrowth.growth' not in src and 'fields84' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-85-divides-3x-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=nondiv=0
for q in range(47,121):
 for X in range(1,101):
  if 3*X%q:continue
  assert q<=3*X and X>=16
  nondiv+=X%q!=0;cases+=1
assert cases and nondiv and 3*16%48==0 and 16%48!=0 and 3*15%45==0
for n in range(13,300):
 r=n-1;R=2*n-1
 assert r+1==n and r>=2 and R==2*r+1
print(json.dumps({'scope':'source and finite threshold controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'divisibility_cases':cases,
 'X_not_divisible_by_q':nondiv,'sharp_X16_example':True},sort_keys=True,indent=2))
