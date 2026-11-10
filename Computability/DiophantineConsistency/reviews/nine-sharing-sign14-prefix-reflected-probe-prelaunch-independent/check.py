#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-reflected-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='7b524e27c3cea5d619a0b327b98fad90fa3f4a908fb3d9beb709342db7a7e550' and sha(p/'source-manifest.json')=='6e2251ce1414f3dafc94eece280ab48d003343e8a4a5a631ff3e49e019821666'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign14PrefixReflectedRow00.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixReflectedRow00' and e['imports']==['DiophantineConsistency.Sign14PrefixCodeRow00'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('(include_str "row00.prefix").toList = encode row00','theorem row00_depth : depth row00 ≤ 24 := by decide','decode p 24 (include_str "row00.prefix").toList','some (SharingSeed14Degree124.row00 p, [])','decode_encode p row00 24 row00_depth []','[List.append_nil, row00_interpret]'):assert t in s
raw=(p/'src/DiophantineConsistency/row00.prefix').read_bytes();assert len(raw)==689 and sha(p/'src/DiophantineConsistency/row00.prefix')==sha(root/'research/nine-sharing-sign14-prefix-formula/row00.prefix')=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6'
stack=[]
for ch in reversed(raw.decode('ascii')):
 if ch in '+-*':a=stack.pop();b=stack.pop();stack.append(1+max(a,b))
 else:assert ch in 'BKCF1234abcdefghijklmno';stack.append(1)
assert len(stack)==1 and stack[0]<=24
for f in ('nine-sharing-sign14-prefix-code-terminal-independent','nine-sharing-sign14-prefix-formula-independent','nine-sharing-sign14-prefix-rows-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'final prefix drift' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','prefix_bytes':len(raw),'independent_prefix_depth':stack[0],'scope':'row00 included bytes decode to staged row under symbolic ports, conditional on Lean; no Lean filesystem/JSON/PDF theorem'},indent=2))
