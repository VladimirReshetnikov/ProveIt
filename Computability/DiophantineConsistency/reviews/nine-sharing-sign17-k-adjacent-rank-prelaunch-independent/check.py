#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-adjacent-rank-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='30ba257f969df82853daf70fbdfccaf679cdca2cad07f573c2f236e90f69eff2' and sha(p/'source-manifest.json')=='eb40db586db5302de5b47f10bc3880a547fd47d9f07892b724c12c7c25be7313'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==18 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
e=rows[-1];assert e['module']=='DiophantineConsistency.Sign17KAdjacentRank' and e['imports']==['DiophantineConsistency.Sign17KActualRank','Mathlib.Order.Fin.Basic'];s=(p/'src/DiophantineConsistency/Sign17KAdjacentRank.lean').read_text()
for t in ('theorem candidate_positions (f : Fin 942 → Fin 942)','(hzero : f 0 = 0)','(hnonzero : ∀ i, i ≠ 0 → f i ≠ 0)','(hadj : ∀ i : Fin 940,','selectorWeight (tile (f i.succ.succ)) <','selectorWeight (tile (f i.castSucc.succ)))','∀ i, physicalMap (f i) = i','Fin.strictAnti_iff_succ_lt'):assert t in s
c=root/'reviews/nine-sharing-sign17-exact-degree-terminal-independent/check.py';assert sha(c)=='ca5e8446ec5cbd623882721b116bd1c767bbe97afcd1689052cdccd97926a5d1';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
failed=root/'reviews/nine-sharing-sign17-k-actual-rank-terminal-independent/check.py';assert sha(failed)=='fa4c93cd653536746bc4a3bf7a2ca6f83804f6b92a74e803b8c30e7810b17bca';subprocess.run([sys.executable,'-I','-S','-B',str(failed)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and '7f0e65d168054f0c977dea30e1268dab68b5754949fc814c8ed33ff9966238f5' in r and '746ee3bbee5b45245056866af653077343b4613078b7251ec1abcca7566b4db8' in r and 'ca401b51912d529f98ac681a875d6932f2007191ba8fb0ad9d8c8a25c652be7c' in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':18,'scope':'conditional actual physicalMap criterion using adjacent weights; candidate hypotheses unproved'},indent=2))
