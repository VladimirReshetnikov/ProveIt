#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-chunk-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='63ad91147d55815818fe4d1b42e038fa4a3c759d7cc186925e48b77fd8eabd07' and sha(p/'source-manifest.json')=='52c915609a52a7da281ca4778d89ef62148b58e59dff203ef15feeeb36b37672'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign14PrefixChunk00.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixChunk00' and e['imports']==['DiophantineConsistency.Sign14PrefixCodeRow00'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert 'encode shared07 = "+*j+*B+b11*B+b1".toList' in s and '(include_str "row00.prefix").toList.take 19' in s and "'-' :: '*' :: '+' :: '+' :: encode shared07" in s
shared2=(root/'research/nine-sharing-sign14-prefix-code-draft/Sign14PrefixCodeShared00.lean').read_text();shared7=(root/'research/nine-sharing-sign14-prefix-code-draft/Sign14PrefixCodeShared01.lean').read_text();assert 'def shared02 : Code := (Code.mul (Code.var 9) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))' in shared2 and 'def shared07 : Code := (Code.add (shared02) ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))))' in shared7
encode02='*j+*B+b11';encoded='+'+encode02+'*B+b1';assert encoded=='+*j+*B+b11*B+b1' and len(encoded)==15
raw=(p/'src/DiophantineConsistency/row00.prefix').read_bytes();assert len(raw)==689 and sha(p/'src/DiophantineConsistency/row00.prefix')==sha(root/'research/nine-sharing-sign14-prefix-formula/row00.prefix')=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6' and raw[:19].decode()=='-*++'+encoded
for f in ('nine-sharing-sign14-prefix-code-terminal-independent','nine-sharing-sign14-prefix-formula-independent','nine-sharing-sign14-prefix-rows-terminal-independent','nine-sharing-sign14-prefix-reflected-probe-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'final prefix drift' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','shared_bytes':15,'file_head_bytes':19,'scope':'first included row00 chunk only, conditional on Lean; remaining 670 bytes and JSON/PDF separate'},indent=2))
