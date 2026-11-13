#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-weight-append-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='252dd3be5cb7b1a5a35c482db479a2ba056c718274d63caccd6c2436e3a96b00' and sha(p/'source-manifest.json')=='d25adec29777a5db12df60f87af49759622decb84baefa28f75b5affa06abb1a'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==16 and rows[:15]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
e=rows[-1];assert e['module']=='DiophantineConsistency.Sign17KWeightAppend' and e['imports']==['DiophantineConsistency.Sign17ExactDegree'];s=(p/'src/DiophantineConsistency/Sign17KWeightAppend.lean').read_text()
for t in ('theorem append_certificates {α β : Type} {m n : ℕ} (f : α → β)','(hleft : ∀ i, f (leftIndex i) = leftValue i)','(hright : ∀ i, f (rightIndex i) = rightValue i)','∀ i, f ((Fin.append leftIndex rightIndex) i) =','(Fin.append leftValue rightValue) i','Fin.addCases'):assert t in s
c=root/'reviews/nine-sharing-sign17-exact-degree-terminal-independent/check.py';assert sha(c)=='ca5e8446ec5cbd623882721b116bd1c767bbe97afcd1689052cdccd97926a5d1';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':16,'scope':'generic finite pointwise certificate concatenation; no concrete union, rank, K or file theorem'},indent=2))
