#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-chunked-row-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='70a83f3bb2b677f6b3ae4501b1e71ddbe4719de6264001e0d36c5540cca74442' and sha(p/'source-manifest.json')=='a9d11a5e8571c4a909ed05db706ac70fc8d0a275418f003b2ef6bb5495081a59'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign14PrefixChunkedRow00.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixChunkedRow00' and e['imports']==['DiophantineConsistency.Sign14PrefixCodeRow00'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert re.findall(r'include_str "(chunk\d\d\.prefix)"',s)==[f'chunk{i:02}.prefix' for i in range(22)]
for t in ('theorem chunks_bytes : chunked = encode row00','theorem row_depth : depth row00 ≤ 24 := by decide','decode p 24 chunked = some (SharingSeed14Degree124.row00 p, [])','decode_encode p row00 24 row_depth []','[List.append_nil, row00_interpret]'):assert t in s
m=json.loads((root/'research/nine-sharing-sign14-prefix-row00-chunks/manifest.json').read_text());parts=[]
for e in m['chunks']:
 q=p/'src/DiophantineConsistency'/e['file'];orig=root/'research/nine-sharing-sign14-prefix-row00-chunks'/e['file'];assert sha(q)==sha(orig)==e['sha256'] and len(q.read_bytes())==e['length'];parts.append(q.read_bytes())
assert len(parts)==22 and b''.join(parts)==(root/'research/nine-sharing-sign14-prefix-formula/row00.prefix').read_bytes()
for f in ('nine-sharing-sign14-prefix-row00-chunks-independent','nine-sharing-sign14-prefix-code-terminal-independent','nine-sharing-sign14-prefix-fragment-terminal-independent','nine-sharing-sign14-prefix-chunk-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and all(f'final prefix drift chunk{i:02}.prefix' in r for i in range(22))
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','chunks':22,'bytes':689,'scope':'decode of 22 embedded fragments conditional on Lean; concatenation to external row is not a Lean file/JSON/PDF theorem'},indent=2))
