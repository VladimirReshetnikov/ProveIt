import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-aux-ring-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'4ece08f14304f68a8984297c9c8c77080b3e18b7668998fa6c3c10ea17cff284','provider_survey.py':'5647fa1bfb1ebca431e5c4ac15beeff475263fbb7ff426b1d0d9508c3e0fcd32','source-manifest.json':'d47b758c4db4b8518c92af7c0333ce947fa9ac4079d85d3dfc320b277fea3a0d','src/DiophantineConsistency/Sign33AuxRing.lean':'1070eb56393abb3f95d7cd1d563d83b4d9e919d0c0ead75dc584f2e34ea950b1'}
for k,h in pins.items():assert sha(p/k)==h,k
src=(p/'src/DiophantineConsistency/Sign33AuxRing.lean').read_text()
for x in ['(hS : 0<S) (hy : 0<y)','(haux : S*S*(absdiff x z)*(absdiff x z)+y*y=1+S*S*y*y)','(ι x-ι z)*(ι x-ι z)-ι y*ι y ≤ 0','Sign33AbsDiffSquare.absdiff_sq x z','Sign33OrderedRing.auxiliary_difference_sign (ι S) (ι x-ι z) (ι y) hSring hyring hauxring']:assert x in src,x
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Sign33AbsDiffSquare','Sign33OrderedRing'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33AuxRing.olean' not in s['links'];assert s['selected'][imports[0]]['sha256']=='f990f1d2f77896b6d52dab63e31e69a0af763c894c5a16d44dc7bb046bce3e65' and s['selected'][imports[1]]['sha256']=='04d0c914a6810e0e449d661e678a20422e500a6cc44e8467b50a2f30e3358c5a'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'Conditional auxiliary norm to proposed ring sign; no source-zero binding or Lean compilation.'},indent=2,sort_keys=True))
