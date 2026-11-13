import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-windows-retry01';old=D/'research/nine-sharing-sign33-windows-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'c5eb6c548eb4bf81205f1cab507835ae096852aa12bbe723dab3bf48c2c007af','provider_survey.py':'b20bdfa2c26708c6bff944dd5d5917d1b6371cad55a4f528fa01e7551fa41b48','source-manifest.json':'be4a2ef552c7e57ed63fbc1e692691119ee2bf8551c925653f736a3864afab67','src/DiophantineConsistency/Sign33Windows.lean':'085fafe11fc49d341a2eeac64a4cc609133f5dd252d049477f6df9187d1ad70b'}
for k,h in pins.items():assert sha(p/k)==h,k
before=(old/'src/DiophantineConsistency/Sign33Windows.lean').read_text();after=(p/'src/DiophantineConsistency/Sign33Windows.lean').read_text();anchor='open ArithmeticPellRecurrence ArithmeticPellFirstIndex\n';added='open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)\n';assert before.count(anchor)==1 and before.replace(anchor,anchor+added)==after
assert sha(old/'provider_survey.py')==sha(p/'provider_survey.py');assert sha(old/'attempt01/state.json')=='accb8bc5fae815c4a739129b4dc6f9f3d4ee83b811033161fbdc6380e352ab6d' and sha(old/'attempt01/Sign33Windows-compile.txt')=='577ca38eca4bcad152d14f6927f7144a5a7e233c5d3e1d650ea1516f23a33d12'
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.ArithmeticPellFirstIndex','DiophantineConsistency.ModelDifferenceRing'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33Windows.olean' not in s['links']
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'Explicit absdiff namespace only, point provider survey and Lean-free preflight; no theorem or bridge yet.'},indent=2,sort_keys=True))
