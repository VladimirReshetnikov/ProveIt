#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-other-fields-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='517b259a2a1121bc34c7aedf74700320f2285c79c5aabdac073327f5d8ad6b76' and sha(p/'source-manifest.json')=='906b65b9ca9890306c55b16efaf4b6fe08336f40a1fffa6fd2c5a835c7eb21b9'
es=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Current14Carrier65QFields','Current14Carrier65OtherFields'];assert [e['module'].split('.')[-1] for e in es]==names
for e,n in zip(es,names):
 q=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',q.read_text(),re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',q.read_text())
assert (p/'src/DiophantineConsistency/Current14Carrier65QFields.lean').read_bytes()==(root/'research/current14-carrier65-q-fields-check/src/DiophantineConsistency/Current14Carrier65QFields.lean').read_bytes()
s=(p/'src/DiophantineConsistency/Current14Carrier65OtherFields.lean').read_text()
for name in ('q','Y','E','k','C','delta','ell','rank','tau','V','S','P','U','W','Z'):assert f'theorem {name}_eval' in s and f').{name} := by' in s
for name,val in [('delta',12),('P',22),('U',62),('W',2),('Z',46)]:assert f'theorem core_{name}_degree' in s and f').{name}).totalDegree ≤ {val}' in s and f'rw [{name}_weight, {name}_eval] at h' in s
for f in ('current14-carrier65-q-fields-terminal-independent','current14-carrier65-other-weights-retry02-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual non-Q factor evaluator bindings and polynomial degree upper bounds'},indent=2))
