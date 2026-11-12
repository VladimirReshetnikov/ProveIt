#!/usr/bin/env python3
"""Independent factor-three projection source/finite review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-divides-3x-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'Divides3X85.lean','bd13831f6d3aa49a336cd90413a8d64ac2ea473aa4c45e71d405925760ebb5c7').decode()
pin(A/'check_source.py','9152dba4f7a164313e7b171faa26858c088aa0a9042844a52296fd5b142e97b4')
receipt=pin(A/'observation.json','a86d2d95519a2ed0140c07cf52cb55d067895960d7f5de327e9b100e8b9d1e22')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-divides-3x-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='c0a148bf5fb18a4fb619e5011ff4df8c6228edf3e534a88cbd4cbfad30530c89'
pin(D/'research/ordinary14-85-p72-exact-indices-draft/P72ExactIndices85.lean','a7e058541155787edeca4b42e28000799a4befad24d9a973072669320f3d6855')
pin(D/'Lean/DiophantineConsistency/Compact44/FreeJPowerProjection.lean','fee95da196452c374b5d6aeaf2b3bb330e8d690224ad8dab523760df79da2749')
for f in ('(hv : ∀ j, 0<v j) (hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'q beta v∣3*X v',
 'P72ExactIndices85Draft.exact_indices p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'let W : V := 4*xx*qq*(v 7)*s','rw [hks,hnR]',
 'have hqY : 0<qq*yy := mul_pos hq hY','mul_left_cancel₀ (ne_of_gt hqY)',
 'H*(xx*yy*qq)','have hH : H=3+qq*D',
 'mod_eq_zero_iff_dvd.mp','exact hm.symm'):
 assert f in src,f
assert 'FreeJPowerProjection.graph_projection' not in src and 'fields84' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-85-p72-exact-indices-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=nondiv=0
for q in range(2,13):
 for X in range(1,19):
  if 3*X%q:continue
  for ys in range(1,5):
   Y=q**3*ys;U=Y*q*q;a=X*Y+Y;H=3+4*a;D0=4*q*q*ys*(X+1)
   assert H==3+q*D0 and H*X%q==0
   for R in (0,5,40):
    W=0;gamma=0;c=7;k=R+1;d=X+a*c+H*X//q
    assert U*d+H*k==U*(X+a*c)+H*(U*gamma+X*Y*q+R+1)
    assert q*(d+H*W)==q*(X+a*c+H*gamma)+H*X
    cases+=1;nondiv+=X%q!=0
assert nondiv and 3*1%3==0 and 1%3!=0
print(json.dumps({'scope':'source and finite projection controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'balance_cases':cases,
 'X_not_divisible_by_q':nondiv,'q3_X1_boundary':True},sort_keys=True,indent=2))
