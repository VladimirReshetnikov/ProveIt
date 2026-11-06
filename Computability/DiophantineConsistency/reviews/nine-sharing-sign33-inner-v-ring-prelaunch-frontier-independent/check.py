import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-inner-v-ring-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'290b69728ebb925d9c1ad6bb2bc0e13ea721c99f387a65f7121f8d9f7dc445fb','provider_survey.py':'0f98c3d7e019682722769b5f63f25761be2a96a353aa8c59d48c381753852809','source-manifest.json':'33a0da46cd0fc9e853a7222032f6999465e115f56b44c8c25e489460c1229ada','src/DiophantineConsistency/Sign33InnerVRing.lean':'d433ca992bad31b325c5e38693dea26fc7731875b4a130132c1c52d451e6f9a9'}
for k,h in pins.items():assert sha(p/k)==h,k
src=(p/'src/DiophantineConsistency/Sign33InnerVRing.lean').read_text()
for x in ['(hc : 0<c) (hT : 0<T) (hf : 0<f) (hi : 0<i)','(hhalf : 2*r<c)','(hstrict : f*f=1+delta a*(i*c*c)*(i*c*c))','0 ≤ ι c*ι T-ι r ∧ 0 ≤ ι f*ι f*(ι c*ι T-ι r)-ι c','Sign33StrongF.strong_norm_f_ge_two a c f i hc hf hi hstrict','Sign33OrderedRing.inner_V_signs (ι c) (ι T) (ι r) (ι f) hcR hTR hhR hfR']:assert x in src,x
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Sign33StrongF','Sign33OrderedRing'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33InnerVRing.olean' not in s['links'];assert s['selected'][imports[0]]['sha256']=='1f314f12d503005ba4d28d4660a0a95bbde87a2751ef77afb2c64d73569c4f6a' and s['selected'][imports[1]]['sha256']=='04d0c914a6810e0e449d661e678a20422e500a6cc44e8467b50a2f30e3358c5a'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'Conditional strong norm and half-window to two proposed ring signs; no source-zero binding or Lean compilation.'},indent=2,sort_keys=True))
