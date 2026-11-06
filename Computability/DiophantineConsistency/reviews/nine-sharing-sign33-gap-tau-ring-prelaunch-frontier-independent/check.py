import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-gap-tau-ring-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'78335cf89e42e2b7a4809b2ec97030761e2e8656a510811d7327aad7e20316a4','provider_survey.py':'3adc88d86f4941fa22513aab35ae6fa987143b357008cf9a76710bf56a078ef7','source-manifest.json':'b76d34db9f8f86f11776d916997d4525ca2d5e80dd8e71aa9fcf11c97f7e956b','src/DiophantineConsistency/Sign33GapTauRing.lean':'9f7bdb432672402030947365c443d2423379dff3a37dbe4284d726d84526ab0f'}
for k,h in pins.items():assert sha(p/k)==h,k
src=(p/'src/DiophantineConsistency/Sign33GapTauRing.lean').read_text()
for x in ['(hq : 1 ≤ q) (hN : 1 ≤ N)','(hgap : 0 < q-F-alpha) (hr : r+2 < E)','0 ≤ (ι q-1)*(ι q-ι F)+ι alpha ∧ 0 ≤ ι E*ι N+ι k-ι r','Sign33OrderedRing.gap_tau_signs','tsub_pos_iff_lt.mp hgap','tsub_add_cancel_of_le hF.le']:assert x in src,x
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Sign33Windows','Sign33OrderedRing'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33GapTauRing.olean' not in s['links'];assert s['selected'][imports[0]]['sha256']=='0fa7c1c14d5b20316780f625ecedf85ea337876f805141dc4adb5db8a23f047b' and s['selected'][imports[1]]['sha256']=='04d0c914a6810e0e449d661e678a20422e500a6cc44e8467b50a2f30e3358c5a'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'Explicit assumed natural windows to two proposed ring signs; no current-source derivation, bridge or Lean compilation.'},indent=2,sort_keys=True))
