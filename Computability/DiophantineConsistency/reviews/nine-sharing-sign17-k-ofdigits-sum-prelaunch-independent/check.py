#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-ofdigits-sum-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='32ccf992e0fc94deb18302637c0d12e5a83d4efaf5e8b9b4f24c2b20d0847347' and sha(p/'source-manifest.json')=='b8bd4faf60ff856fac97a7a0e85883fa7b7da2553a2a3c23a794aa7cbf4778da'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign17KOfDigitsSum.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign17KOfDigitsSum' and e['imports']==['DiophantineConsistency.Sign17KWeightUnion942'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('theorem ofDigits_ofFn_sum (r : ℕ) (n : ℕ) (v : Fin n → ℕ)', 'Nat.ofDigits r (List.ofFn v) = ∑ i : Fin n, v i * r ^ i.val', 'induction n generalizing v', 'List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ', '#print axioms DiophantineConsistency.Sign17KOfDigitsSum.ofDigits_ofFn_sum'):assert t in s
# Little-endian identity checked on arbitrary representative vectors, including bases zero and one.
for r in range(5):
 for v in ([],[0],[3],[1,4,2],[0,0,4,1]):
  acc=0
  for x in reversed(v):acc=x+r*acc
  assert acc==sum(x*r**i for i,x in enumerate(v))
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-ranking-witness-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic little-endian ofDigits finite power sum only; no K/file theorem'},indent=2))
