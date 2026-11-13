#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-dag-lemma-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='0d1278024ffb35922d22002ccfc1058d2f8f272632d4d19c321c2f36c35c7e14' and sha(p/'source-manifest.json')=='bae1351912aee56557b9114af3331765cd164ac91aeb94119fabfdcb07fe7ea8'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign14PrefixDagShared07.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixDagShared07' and e['imports']==['DiophantineConsistency.Sign14PrefixCodeRow00'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert '(include_str "fragment007.prefix").toList = encode shared07' in s
q=p/'src/DiophantineConsistency/fragment007.prefix';assert q.read_bytes()==b'+*j+*B+b11*B+b1' and sha(q)==sha(root/'research/nine-sharing-sign14-prefix-dag-fragments/fragment007.prefix')=='0c20087a3433dde1bd4f2b39fbc01b9a1d6789cd90aa49fa83a0d48bd8eabddb'
for f in ('nine-sharing-sign14-prefix-dag-fragments-independent','nine-sharing-sign14-prefix-code-terminal-independent','nine-sharing-sign14-prefix-fragment-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'final prefix drift' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','fragment_bytes':15,'scope':'one separately included shared07 fragment; no Lean full-file/JSON/PDF theorem'},indent=2))
