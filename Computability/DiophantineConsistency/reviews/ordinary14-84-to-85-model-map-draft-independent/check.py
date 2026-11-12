#!/usr/bin/env python3
"""Independent model-map source and finite review; no Lean invocation."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-to-85-model-map-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'ModelMap.lean','2c0d149a4147e813aed2d1caf3ab0de1b0c903092852fc551a1ff9424f38f8ed').decode()
pin(A/'check_source.py','a0ea2eaf20340bd203c4dd5af52f2e4162c8b7be54c2f83071edffa9efa0a6a0')
receipt=pin(A/'observation.json','0bbef63d1045cca2b28f97a6b08032bca69feb6252d5c0cb8dd68425b9914492')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-to-85-model-map-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='fad2c257665ce3dce5bd22f1bb0abba6bf0d61b1f1348fb0e475ebdc45e16f58'
for path,h in {
 'ordinary14-84-p72-exact-indices-draft/P72ExactIndices.lean':'504541280d0258606602d9d22af9c6573b8749dfdbc0dd243d77618e6f919640',
 'ordinary14-modified-carrier-gamma-model-draft/CarrierGamma.lean':'5d8dc10ca61726a6c2b939c2d98a784fb06b702348b15fa657badf7545984d3a',
 'ordinary14-84-85-conditional-model-draft/ConditionalComparison.lean':'204cf248239f6a070176c407f1d8d2ddb8506afad9784e79ac5ab0a0d2638790',
}.items():pin(D/'research'/path,h)
for f in ('(hMC : MC<beta) (hMF : MF<2*beta)',
 '(hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'P72ExactIndices84Draft.exact_indices p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'let W : V := 4*X*q*(v 7)*s','rw [hks,hnR]',
 'have hc : c=ycoord R a := by rw [←hmR]; exact hy.symm',
 'have hd : d=xcoord R a := by rw [←hmR]; exact hx.symm',
 'gamma_gt_from_modified_balance U H d X Y a c (v 12) k R W q (v 6)',
 'hU hY hq hX ha hH hR3 hc hd hk hbal',
 'map_84_to_85 p beta v hport hv hgamma hz'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-p72-exact-indices-draft-independent','ordinary14-modified-carrier-gamma-model-draft-independent','ordinary14-84-85-conditional-model-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=0
for q,X,yslot,s in itertools.product(range(1,9),range(1,8),range(1,7),range(6)):
 Y=q**3*yslot;U=Y*q*q;W=4*X*q*yslot*s
 assert U*W==4*X*Y*Y*s
 for n in (1,2,7):
  R=2*n-1;k=2*n+4*X*Y*Y*s
  assert k==R+1+U*W;cases+=1
print(json.dumps({'scope':'source and finite quotient controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'quotient_cases':cases,
 'independent_dependency_reviews':3},sort_keys=True,indent=2))
