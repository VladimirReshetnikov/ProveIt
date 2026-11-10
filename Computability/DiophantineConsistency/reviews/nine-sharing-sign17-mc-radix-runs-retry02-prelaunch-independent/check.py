#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-mc-radix-runs-retry02-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='cec8beb3d2f9e6f436cc9ab3e3e41e1430e145b0d91cb1349e9decaf5b292e0f' and sha(p/'source-manifest.json')=='85752488724fbf6ba62a515c100d7fbf8c7715214508f4ad1444b934f05eb7b9'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-exact-degree-check/source-manifest.json').read_text())['rows'];assert len(rows)==17 and rows[:15]==prior
for e in rows:
 name=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports']
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',src.read_text())
assert rows[15]['imports']==['DiophantineConsistency.Sign17ExactDegree','Mathlib.Algebra.Ring.GeomSum'] and rows[16]['imports']==['DiophantineConsistency.Sign17MCRadixCore']
core=(p/'src/DiophantineConsistency/Sign17MCRadixCore.lean').read_text();s=(p/'src/DiophantineConsistency/Sign17MCRadixRuns.lean').read_text();assert all(t in core for t in ('theorem ofDigits_map_range','theorem ofDigits_maskList_add','theorem ofDigits_maskList','open Finset LowMaskCoding'))
runs=[(int(a),int(b)) for a,b in re.findall(r'List.replicate (\d+) \(radix - (\d+)\)',s)];assert runs==[(951,2),(9,1),(26,2),(18,1),(1,2),(1006,1)];digits=[v for count,v in runs for _ in range(count)];assert len(digits)==2011 and {i for i,v in enumerate(digits) if v==2}==set(range(951))|set(range(960,986))|{1004};assert all(x in s for x in ('theorem maskList_runs','theorem low_port_runs','Sign17MCRadixCore.ofDigits_maskList','simp only [Sign17MCRadixCore.maskList, List.length_map'))
old=root/'research/nine-sharing-sign17-mc-radix-runs-retry-check';oldrows=json.loads((old/'source-manifest.json').read_text())['rows'];assert rows[:16]==oldrows[:16]
oldsrc=(old/'src/DiophantineConsistency/Sign17MCRadixRuns.lean').read_text();assert oldsrc.replace('    decide\n  · intro i hi hj','  · intro i hi hj',1)==s
oldrun=(old/'run.py').read_text();newrun=(p/'run.py').read_text();assert oldrun.replace('mc-radix-runs-retry-20261110','mc-radix-runs-retry02-20261110').replace('557c00927c981d903a588f3e9ecb3b3a72571c45a14119229301f20856833cfc','85752488724fbf6ba62a515c100d7fbf8c7715214508f4ad1444b934f05eb7b9')==newrun
failure=root/'reviews/nine-sharing-sign17-mc-radix-runs-retry-terminal-independent/check.py';assert sha(failure)=='409b3d233840562ac565d828b3b403fc57f82ac831b46dcb559555ce22f642d8';subprocess.run([sys.executable,'-I','-S','-B',str(failure)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'f7b10e5ff78ec4af74841d77f6d5c4776c3c31c67df7d3dda1d91b79a1ad4ff0' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':17,'scope':'proposed generic digit core and symbolic mask runs; import compatibility untested, no Lean result or file binding'},indent=2))
