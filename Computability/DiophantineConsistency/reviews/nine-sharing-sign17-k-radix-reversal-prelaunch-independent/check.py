#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-radix-reversal-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='273eada92d2219aee8d5ab8bd75817effee170c24376e1c5c1a1bc901736b3ff' and sha(p/'source-manifest.json')=='607b79cc37c7b5f709b0a0dcaf8d945ba0d88c08e4928e40c9133f9e47926a73';e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KRadixReversal.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KRadixReversal' and e['imports']==['DiophantineConsistency.Sign17KOfDigitsSum'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='f49e13456bcc9e56672f42f60d8ee8df8bd242b0ee3498a6d642a1b7fc959a50' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('theorem rev_bijective (n : ℕ)', 'theorem ofDigits_reversed (r n : ℕ) (v : Fin n → ℕ)','v i * r ^ (n - (i.val + 1))','theorem ofDigits_increment (r n : ℕ) (v : Fin n → ℕ) (k : Fin n)','v i + if i = k then 1 else 0','Nat.ofDigits r (List.ofFn v) + r ^ k.val'):assert t in s
for r in range(5):
 for v in ([],[1],[2,0,4],[0,3,1,5]):
  n=len(v);rev=sum(v[n-i-1]*r**i for i in range(n));assert rev==sum(v[i]*r**(n-(i+1)) for i in range(n))
  for k in range(n):assert sum((x+(i==k))*r**i for i,x in enumerate(v))==sum(x*r**i for i,x in enumerate(v))+r**k
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-ofdigits-sum-retry-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-ofdigits-sum-retry-check/attempt01/state.json').read_text());assert prior['status']=='PASS';obj=Path('/tmp/nine-sharing-sign17-k-ofdigits-sum-retry-20261110/lib/DiophantineConsistency/Sign17KOfDigitsSum.olean');assert sha(obj)==prior['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic reversal/increment ingredients only, no K/digit bounds/file theorem'},indent=2))
