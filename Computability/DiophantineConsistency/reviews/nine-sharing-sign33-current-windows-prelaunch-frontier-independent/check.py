import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-current-windows-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'2306604b919e07a84eb7367dc0219f64a322f32c4b4ed8ad2fbb56fd5f4ff084','provider_survey.py':'4e21460e1254bc06134ad90bd8666631ce8d631a3e387a302e0ed370fb3f7146','source-manifest.json':'a1c933c9ecc7de1674d0b8bc46770d09576e177f0ecdf7eb874b7532a488e7b2','src/DiophantineConsistency/Sign33CurrentWindows.lean':'ac17e913b7abcd7a398221ff9e93fc4b6648eece6ba27f6737a600eaaa4d9ed3'}
for k,h in pins.items():assert sha(p/k)==h,k
src=(p/'src/DiophantineConsistency/Sign33CurrentWindows.lean').read_text()
for x in ['ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression v','let w : Fin 14 → V := fun j => v j+1','let q := (CurrentMasks2011.beta : V)*w 0+1','let E := (w 8*q)*(w 7*q^3)','let c := (w 10+w 11)*(w 7*q^3)+w 10','CurrentMasks2011.highPort+CurrentMasks2011.beta : ℕ','0<q-w 1-w 2 ∧ r+2<E ∧ 2*r<c','ArithmeticCarrierSoundness2011.current_bounds','ArithmeticCarrierSoundness2011.current_natural_equations v hz','Sign33Windows.windows_from_maintained_norms']:assert x in src,x
for j in range(14):assert f'(w {j})' in src and f'(hw {j})' in src,j
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Sign33Windows','DiophantineConsistency.ArithmeticCarrierSoundness2011'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33CurrentWindows.olean' not in s['links'];assert s['selected'][imports[0]]['sha256']=='0fa7c1c14d5b20316780f625ecedf85ea337876f805141dc4adb5db8a23f047b'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'Proposed current source zero to three natural windows; no graph/sign bridge or Lean compilation.'},indent=2,sort_keys=True))
