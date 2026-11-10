#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-stream-bump-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='127152cb15ce31ed78b62347e5b268a0cdbc1cbd1a549ec1e6aed6aaab6a19ba' and sha(p/'source-manifest.json')=='d765c71437892278f23d113238dd41e71a307c34e0c42e5670d01460d0f88580'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KStreamBump.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KStreamBump' and e['imports']==['DiophantineConsistency.Sign17KStreamReversal'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='9eb0b032d4e5d8529c75faceda9a44f38002b6aaeed9369bb2f285805110d522' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('theorem ofFn_bump (n : ℕ) (v : Fin n → ℕ) (k : Fin n)','(List.ofFn v).set k.val (v k + 1)','theorem block_as_reverse_set (v : Fin 986 → ℕ)','((List.ofFn v).reverse).set 984 (v ⟨1, by decide⟩ + 1)'):assert t in s
up=(root/'research/nine-sharing-sign17-k-radix-stream-retry-draft/Sign17KRadixStream.lean').read_text();assert 'List.ofFn (fun i : Fin 986 => v i.rev + if i = ⟨984, by decide⟩ then 1 else 0)' in up and 986-1-984==1 and 20+984==1004
for n in range(1,30):
 v=list(range(n))
 for k in range(n):
  lhs=[x+int(i==k) for i,x in enumerate(v)];rhs=v.copy();rhs[k]=v[k]+1;assert lhs==rhs
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-stream-reversal-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-stream-reversal-check/attempt01/state.json').read_text());assert prior['status']=='PASS';obj=Path('/tmp/nine-sharing-sign17-k-stream-reversal-20261110/lib/DiophantineConsistency/Sign17KStreamReversal.olean');assert sha(obj)==prior['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic one-coordinate list update and symbolic K block specialization only; fixture/file linkage separate'},indent=2))
