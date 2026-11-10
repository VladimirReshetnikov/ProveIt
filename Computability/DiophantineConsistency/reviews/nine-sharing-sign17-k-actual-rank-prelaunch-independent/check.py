#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-actual-rank-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='405c630cad2a2db3d5d5785accedb595e63017563a5b120b2cc55fd52e4c6ded' and sha(p/'source-manifest.json')=='307e5e6d090bed5839438f9d8a5e3dc93afa0118ffb8ac441a07bee41095b197'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==17 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
e=rows[-1];assert e['module']=='DiophantineConsistency.Sign17KActualRank' and e['imports']==['DiophantineConsistency.Sign17KRankGeneric','DiophantineConsistency.MFWangTiles942Permutation'];s=(p/'src/DiophantineConsistency/Sign17KActualRank.lean').read_text()
for t in ('theorem candidate_positions (f : Fin 942 → Fin 942)','(hzero : f 0 = 0)','(hnonzero : ∀ i, i ≠ 0 → f i ≠ 0)','(hdesc : ∀ i j, i < j → i ≠ 0 →','selectorWeight (tile (f j)) < selectorWeight (tile (f i)))','∀ i, physicalMap (f i) = i','Sign17KRankGeneric.candidate_positions physicalMap f','physical_lt_iff_weight'):assert t in s
c=root/'reviews/nine-sharing-sign17-exact-degree-terminal-independent/check.py';assert sha(c)=='ca5e8446ec5cbd623882721b116bd1c767bbe97afcd1689052cdccd97926a5d1';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
failed=root/'reviews/nine-sharing-sign17-k-rank-generic-terminal-independent/check.py';assert sha(failed)=='134bc0de4ec52a1c9c7099de9fa73dec541733d083f5f04c1821fbf359533c15';subprocess.run([sys.executable,'-I','-S','-B',str(failed)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and '746ee3bbee5b45245056866af653077343b4613078b7251ec1abcca7566b4db8' in r and 'ca401b51912d529f98ac681a875d6932f2007191ba8fb0ad9d8c8a25c652be7c' in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':17,'scope':'conditional actual physicalMap specialization; candidate hypotheses unproved'},indent=2))
