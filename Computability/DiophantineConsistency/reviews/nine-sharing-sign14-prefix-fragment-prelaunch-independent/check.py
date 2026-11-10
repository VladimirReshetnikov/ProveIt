#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-fragment-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='6bf4d5d67fddbb3f63b2444de84337f6f45de1efdb32f2dc4aeead04be230f05' and sha(p/'source-manifest.json')=='7b512012ce595a0ee93f87d45217963072723a8741085c09981ead9372f58fe7'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign14PrefixFragment00.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixFragment00' and e['imports']==['DiophantineConsistency.Sign14PrefixCodeRow00'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert 'encode shared07 = "+*j+*B+b11*B+b1".toList' in s and '(include_str "chunk00.prefix").toList =' in s and "'-' :: '*' :: '+' :: '+' :: encode shared07" in s and 'row00.prefix' not in s
q=p/'src/DiophantineConsistency/chunk00.prefix';raw=q.read_bytes();assert len(raw)==19 and raw==b'-*+++*j+*B+b11*B+b1' and sha(q)==sha(root/'research/nine-sharing-sign14-prefix-row00-chunks/chunk00.prefix')=='68aa79a77a39d939830530edf7d9642f272d82473de072561b01181bf8d585e6'
for f in ('nine-sharing-sign14-prefix-row00-chunks-independent','nine-sharing-sign14-prefix-code-terminal-independent','nine-sharing-sign14-prefix-chunk-terminal-independent','nine-sharing-sign14-prefix-chunk-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'final prefix drift' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','fragment_bytes':19,'scope':'separately included fragment only; external chunk concatenation is not Lean full-file or JSON/PDF theorem'},indent=2))
