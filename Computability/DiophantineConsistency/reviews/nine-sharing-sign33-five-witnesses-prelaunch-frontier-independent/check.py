import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-five-witnesses-check';draft=D/'research/nine-sharing-sign33-five-witnesses-draft/Sign33FiveWitnesses.lean'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'f786a9f8d979f3820d849fb8de0901084a9bffe7911f132766b70baa4007e5f0','provider_survey.py':'01af7f4da770a2fa4bc8d24e51da8cc65340cb7bdc485dc3ba8c116db46eeb67','source-manifest.json':'64a45d9f65c78722241b89386c704283820585788985a89b0ac3af6ad258eab3','src/DiophantineConsistency/Sign33FiveWitnesses.lean':'dbecb8b85c1e3f54446b50eb8e2b68e6dc5f389d49493d14ffe84962f20da893'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(draft)==pins['src/DiophantineConsistency/Sign33FiveWitnesses.lean'];src=draft.read_text()
for x in ['(hq : 1≤q) (hN : 1≤N) (hgap : 0<q-F-alpha) (hr : r+2<E)','(hc : 0<c) (hT : 0<T) (hf : 0<f) (hi : 0<i) (hhalf : 2*r<c)','(hstrict : f*f=1+delta a*(i*c*c)*(i*c*c))','(hS : 0<S) (hy : 0<y)','S*S*(absdiff x z)*(absdiff x z)+y*y=1+S*S*y*y','∃ gap tau inner v negative : V','ι negative = ι y*ι y-(ι x-ι z)*(ι x-ι z)','sub_nonneg.mpr (sub_nonpos.mp','hgap\'.symm, htau\'.symm, hinner\'.symm, hv\'.symm, hnegative\'.symm']:assert x in src,x
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Sign33GapTauRing','DiophantineConsistency.Sign33InnerVRing','DiophantineConsistency.Sign33AuxRing'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and 'DiophantineConsistency/Sign33FiveWitnesses.olean' not in s['links']
for k,h in zip(imports,['3e7fd736fbb3f2ded242eae53e34df62c87709f755752724c6afd028546606bb','bb4c20461196accbd1e3e3914f9ab6637f2142f5366150e29caf3b037d3371da','c811fe71c42029cf613637374432ae92f636dad314d2b3b756690831aa5af621']):assert s['selected'][k]['sha256']==h
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'Conditional five model-natural representatives; no concrete seed valuation, zero bridge or Lean compilation.'},indent=2,sort_keys=True))
