#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-reflection-retry02-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='1edd570fd1578c233c129072aeb344623e50d1b13f18fb3c04c9fa27fac355a2' and sha(p/'source-manifest.json')=='e278c4b4e39e5f559b97f40f617369207df97b142dd1c2bf0143f5f41687bee8'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign14PrefixReflection.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixReflection' and e['imports']==['DiophantineConsistency.Sign14PrefixParser'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
old=(root/'research/nine-sharing-sign14-prefix-reflection-retry01-draft/Sign14PrefixReflection.lean').read_text()
for op in ('add','sub','mul'):
 a='simp only [Option.bind_some, Prod.fst, Prod.snd]'
 b='change (match decode p n (encode b ++ tail) with\n            | none => none\n            | some (right, rest) => some (Expr.'+op+' (interpret p a) right, rest)) = _'
 assert a in old;old=old.replace(a,b,1)
assert old==s
for x in ('nine-sharing-sign14-prefix-reflection-retry01-terminal-independent',):
 c=root/'reviews'/x/'check.py';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic prefix decode/encode with depth fuel, conditional on subsequent Lean run; no long-row, JSON, or PDF theorem'},indent=2))
