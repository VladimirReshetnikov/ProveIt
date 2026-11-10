#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-ofdigits-sum-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='f5ff7127b21e028cfc591d3286bdc2624b2dff5164d68e8310b5e7d5bd19fc02' and sha(p/'source-manifest.json')=='097a646e95d90f8c0cdcdc07541dc9894b30d4f525ad4221cba23926816ef395'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign17KOfDigitsSum.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign17KOfDigitsSum' and e['imports']==['DiophantineConsistency.Sign17KWeightUnion942'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('theorem ofDigits_ofFn_sum (r : ℕ) (n : ℕ) (v : Fin n → ℕ)', 'Nat.ofDigits r (List.ofFn v) = ∑ i : Fin n, v i * r ^ i.val', 'induction n with', 'List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ', '#print axioms DiophantineConsistency.Sign17KOfDigitsSum.ofDigits_ofFn_sum'):assert t in s
# Little-endian identity checked on arbitrary representative vectors, including bases zero and one.
for r in range(5):
 for v in ([],[0],[3],[1,4,2],[0,0,4,1]):
  acc=0
  for x in reversed(v):acc=x+r*acc
  assert acc==sum(x*r**i for i,x in enumerate(v))
old=(root/'research/nine-sharing-sign17-k-ofdigits-sum-check/src/DiophantineConsistency/Sign17KOfDigitsSum.lean').read_text();assert old.replace('induction n generalizing v with','induction n with')==s
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-ranking-witness-independent','nine-sharing-sign17-k-ofdigits-sum-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic little-endian ofDigits finite power sum only; no K/file theorem'},indent=2))
