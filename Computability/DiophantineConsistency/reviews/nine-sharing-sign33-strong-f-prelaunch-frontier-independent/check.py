import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-strong-f-check';draft=D/'research/nine-sharing-sign33-signs-draft/Sign33Draft.lean'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'e15ac2c69851e305f0c7b948046bcf323e0a8d047e37de12afae07937a0d20bb','provider_survey.py':'75772d73291dbbdbfc03160dea46e73e75b2fc2162b69dcc25b8aa17fefc9f43','source-manifest.json':'9cd871eb0515a2fe4f4505f4cd80830ef68f818d73b696fe9c23c8fd32533d1f','src/DiophantineConsistency/Sign33StrongF.lean':'6dae60f7b531a8af18bc2567f478ae3f26cab5b9d1195651c5c84e5a27bc47cd'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(draft)=='c6cf5a3c39c00188050a71f5a7e95d93884344db9b275bc095b224527a49fb4d';ds=draft.read_text();block=ds[ds.index('theorem strong_norm_f_ge_two'):ds.index('\n/-- Proposed direct application',ds.index('theorem strong_norm_f_ge_two'))];src=(p/'src/DiophantineConsistency/Sign33StrongF.lean').read_text();assert block in src
for x in ['(hc : 0<c)','(hf : 0<f)','(hi : 0<i)','(hstrict : f*f=1+delta a*(i*c*c)*(i*c*c)) : 2≤f']:assert x in block
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;imports=['DiophantineConsistency.ArithmeticPellFirstIndex','DiophantineConsistency.ModelDifferenceRing'];assert rows[0]['imports']==imports
s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33StrongF.olean' not in s['links']
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'Point-in-time survey and exact copied source, no Lean proof, sign bridge or endpoint.'},indent=2,sort_keys=True))
