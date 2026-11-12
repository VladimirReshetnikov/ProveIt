#!/usr/bin/env python3
"""Independent positive equivalence wrapper review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-85-model-equivalence-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'ModelEquivalence.lean','4a0bb28f91614ee0a30046e8072fa246f2f55117a059c7a56becae95cedeedcc').decode()
pin(A/'check_source.py','12ac29b10750072eea3558c584643507de8894a089a63c9f6f0055f0c8ec5773')
receipt=pin(A/'observation.json','24d7bc3a6927b4c4b8f95ebc0fbee7ee03ce1092120cfd05224ca71be600d77b')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-85-model-equivalence-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='82b881cee65c53a3fbb1e0c833ff9f31ff5372bcbd5b8a3ab7e9448ceb0a8bca'
for path,h in {
 'ordinary14-84-to-85-model-map-draft/ModelMap.lean':'2c0d149a4147e813aed2d1caf3ab0de1b0c903092852fc551a1ff9424f38f8ed',
 'ordinary14-85-to-84-model-map-draft/ModelMap85To84.lean':'8f82ad48c583b1bb6b91bf94f78a39097b0462b827cce748c148639387810368',
}.items():pin(D/'research'/path,h)
for f in ('(hbeta : 0<beta) (hbeta46 : 46≤beta) (ht : 4≤t) (hradix : beta=Exp.exp t-1)',
 '(hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)',
 '(hMCcast : (p 2 : DiffRing V)=ι MC) (hMFcast : (p 3 : DiffRing V)=ι MF)',
 '(hMC : MC<beta) (hMF : MF<2*beta)',
 'InternalZero (P84QcubeGraph.graph p).output v) ↔',
 'InternalZero (P85QcubeGraph.graph p).output v)',
 'ModelMap84To85Draft.positive_map p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'ModelMap85To84Draft.positive_map p beta K MC MF t v hbeta hbeta46 ht hradix\n      hport hK hMCcast hMFcast hMC hMF hv hz'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-to-85-model-map-draft-independent','ordinary14-85-to-84-model-map-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'source interface and dependency review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'independent_direction_reviews':2},sort_keys=True,indent=2))
