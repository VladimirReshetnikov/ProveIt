import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-strong-f-retry01';old=D/'research/nine-sharing-sign33-strong-f-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'dc29a2628ab57d87bde74ab5663f72ef5f86e57b9cb70d58c260f03a2f3f9d22','provider_survey.py':'75772d73291dbbdbfc03160dea46e73e75b2fc2162b69dcc25b8aa17fefc9f43','source-manifest.json':'13f9f73a55994930f6b7e43581dd25dca70aecc1cc49a5247059a3731b5aba68','src/DiophantineConsistency/Sign33StrongF.lean':'df4419d685971b45d91f3f5ccc6f5f3b841bcf2beeb225a74117cfe46d8bbf1e'}
for k,h in pins.items():assert sha(p/k)==h,k
before=(old/'src/DiophantineConsistency/Sign33StrongF.lean').read_text();after=(p/'src/DiophantineConsistency/Sign33StrongF.lean').read_text();a='  simpa using lt_iff_succ_le.mp hgt';b='  simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hgt';assert before.count(a)==1 and before.replace(a,b)==after
assert sha(old/'provider_survey.py')==sha(p/'provider_survey.py');assert sha(old/'attempt01/state.json')=='80899a5be35a092903a15ad21e8aba56fbd89b46daa045ea6862c51e6587719a' and sha(old/'attempt01/Sign33StrongF-compile.txt')=='6f7c5110898c0c8670d6d5d9e05caf79d75d461235acce36ad30804adf34f47c'
runner=(p/'run.py').read_text();oldrunner=(old/'run.py').read_text();assert "-M2800" in runner and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner and "-M2800" in oldrunner
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.ArithmeticPellFirstIndex','DiophantineConsistency.ModelDifferenceRing'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33StrongF.olean' not in s['links']
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'overlay_links':len(s['links']),'scope':'One tactic-only source edit, point provider survey and Lean-free preflight; no theorem or bridge yet.'},indent=2,sort_keys=True))
