#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-rank-generic-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='153f72c324055edc68bf95495ebe32fc060db164fa0e8b7af3b86063e068add0' and sha(p/'source-manifest.json')=='81bc5f1a17d6d438e8f1f5fd29e517963b12be8be6857366ef24919859ae1eae'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==16 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
e=rows[-1];assert e['module']=='DiophantineConsistency.Sign17KRankGeneric' and e['imports']==['DiophantineConsistency.Sign17ExactDegree','Mathlib.Order.WellFounded'];s=(p/'src/DiophantineConsistency/Sign17KRankGeneric.lean').read_text()
for t in ('theorem candidate_positions (rank f : Fin 942 → Fin 942) (weight : Fin 942 → ℕ)','(hrankzero : rank 0 = 0) (hrankinj : Function.Injective rank)','(horder : ∀ a b, a ≠ 0 → b ≠ 0 →','(hzero : f 0 = 0)','(hnonzero : ∀ i, i ≠ 0 → f i ≠ 0)','(hdesc : ∀ i j, i < j → i ≠ 0 → weight (f j) < weight (f i))','∀ i, rank (f i) = i'):assert t in s
c=root/'reviews/nine-sharing-sign17-exact-degree-terminal-independent/check.py';assert sha(c)=='ca5e8446ec5cbd623882721b116bd1c767bbe97afcd1689052cdccd97926a5d1';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
failed=root/'reviews/nine-sharing-sign17-k-rank-certificate-terminal-independent/check.py';assert sha(failed)=='23a83c21df5884c307034954d625e141e615acd38c8e8024b524ef151730a94f';subprocess.run([sys.executable,'-I','-S','-B',str(failed)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'ca401b51912d529f98ac681a875d6932f2007191ba8fb0ad9d8c8a25c652be7c' in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':16,'scope':'generic rank criterion with explicit assumptions; no actual physicalMap specialization'},indent=2))
