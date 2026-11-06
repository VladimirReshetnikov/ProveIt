import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-absdiff-square-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'046d5ce155df2e3d6f0d3a942d5f8ba6acd12255ded5802c65195d96f59e8e9d','provider_survey.py':'835b3711cc6b19758bbe1f59f422528a4bada5eeec5895aaaea8fcde8e2025ad','source-manifest.json':'73f07bfc9e6c4bc0bd3f1e688df7ce37267429bef47a2f66295651eff8988476','src/DiophantineConsistency/Sign33AbsDiffSquare.lean':'6dda96f620b4df528aab6b913732f86f68516ad04db0727a7aa84a806be5c0bf'}
for k,h in pins.items():assert sha(p/k)==h,k
src=(p/'src/DiophantineConsistency/Sign33AbsDiffSquare.lean').read_text()
for x in ['theorem absdiff_sq (x y : V)','ι (absdiff x y) * ι (absdiff x y) = (ι x-ι y)*(ι x-ι y)','rcases le_total y x with h | h','tsub_add_cancel_of_le h','tsub_eq_zero_of_le h']:assert x in src,x
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.ArithmeticPellHalfIndex','DiophantineConsistency.ModelDifferenceRing'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33AbsDiffSquare.olean' not in s['links'];assert s['selected'][imports[1]]['sha256']=='cf2b32cb1e4777b7cff73c34ed7334a105f705912fa987e9f7f9a316fef192f0'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'Local absdiff-square proposal and point producer checks only; no Lean proof, sign bridge or iPRA endpoint.'},indent=2,sort_keys=True))
