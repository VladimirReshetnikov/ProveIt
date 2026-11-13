#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-reflection-retry03-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='c395ede94e4c67ec97f18815974c58ecd9f97c7b3801092b084065c102ac8f22' and sha(p/'source-manifest.json')=='f9852f2a85fc253d60c1a7ffa9288aa682b1a2558b1399075c2007115b9af035'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign14PrefixReflection.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixReflection' and e['imports']==['DiophantineConsistency.Sign14PrefixParser'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
old=(root/'research/nine-sharing-sign14-prefix-reflection-retry02-draft/Sign14PrefixReflection.lean').read_text()
for op in ('add','sub','mul'):
 a='change (match decode p n (encode b ++ tail) with\n            | none => none\n            | some (right, rest) => some (Expr.'+op+' (interpret p a) right, rest)) = _';assert a in old;old=old.replace(a,'dsimp',1)
assert old==s
c=root/'reviews/nine-sharing-sign14-prefix-reflection-retry02-terminal-independent/check.py';assert sha(c)=='aac90dfab31c3e567365cdf9ab1e4b7ecd2b736e9316c71a7a652711b4f6db06';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic prefix decode/encode with depth fuel, conditional on Lean run; no long-row, JSON, or PDF theorem'},indent=2))
