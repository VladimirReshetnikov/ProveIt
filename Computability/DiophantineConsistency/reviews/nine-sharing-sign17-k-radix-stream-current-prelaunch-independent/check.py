#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-radix-stream-current-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='a9bc166e0b9d91fc5caaaa07c4a5725d6e25694a9787b741e9ea74623058f49c' and sha(p/'source-manifest.json')=='b67bcb59e17ac7c45c165b283e551e3bba20f67578ee9d32dd90d0a8d08150c9'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KRadixStreamCurrent.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KRadixStreamCurrent' and e['imports']==['DiophantineConsistency.Sign17KRadixStream','DiophantineConsistency.Sign17KLiteralCoefficients'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='9174d5b76f518bc68726e7bd1697475b4bbeea28128a14c92728f4e4789bcafb' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for x in ('Nat.ofDigits radix','Sign17KRadixStream.digits Sign17KLiteralCoefficients.literal','Sign17KRadixStream.digit_value','Sign17KLiteralCoefficients.K_literal.symm'):assert x in s
for f in ('nine-sharing-sign17-k-radix-stream-retry-terminal-independent','nine-sharing-sign17-k-literal-coefficient-union-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
states=[]
for stem,dir in [('nine-sharing-sign17-k-radix-stream-retry-check','/tmp/nine-sharing-sign17-k-radix-stream-retry-20261110'),('nine-sharing-sign17-k-literal-coefficient-union-retry-check','/tmp/nine-sharing-sign17-k-literal-coefficient-union-retry-20261110')]:
 st=json.loads((root/'research'/stem/'attempt01/state.json').read_text());assert st['status']=='PASS';base=Path(dir);m={str(Path(k).relative_to(base/'lib')):v for k,v in st['overlay_links'].items()};states.append((st,base,m))
a,b=states;overlap=set(a[2])&set(b[2]);assert len(overlap)==1132 and all(a[2][k]==b[2][k] for k in overlap);init=a[0]['rows'][0]['dependencies']['Init'];assert all(row['dependencies']['Init']==init for st,_,_ in states for row in st['rows'])
for st,base,_ in states:
 for row in st['rows']:
  q=base/'lib/DiophantineConsistency'/(row['module']+'.olean');assert q.is_file() and sha(q)==row['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','provider_overlay_overlap':len(overlap),'scope':'proposed in-Lean symbolic K stream identity, no digit-bound/byte/file theorem'},indent=2))
