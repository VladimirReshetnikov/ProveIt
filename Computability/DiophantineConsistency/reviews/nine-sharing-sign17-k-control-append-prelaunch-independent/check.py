#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-control-append-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d302330866b8310055e2780d7807fab705a5484ae14eedd41e80779e344e5ec0' and sha(p/'source-manifest.json')=='948bb98030315e5f5035964a7ec6bb823dd65442389c466d8b94c1088328a94c'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign17KControlAppend.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign17KControlAppend' and e['imports']==['DiophantineConsistency.Sign17KRankedRawWord'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('theorem append_power_sum {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)','(r offset : ℕ)','(Fin.append a b) i * r ^ (1005 - (offset + i.val))','a i * r ^ (1005 - (offset + i.val))','b i * r ^ (1005 - ((offset + m) + i.val))','Fin.sum_univ_add'):assert t in s
for f in ('nine-sharing-sign17-k-ranked-rawword-retry-terminal-independent','nine-sharing-sign17-k-control-coefficients-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic shifted Fin.append power-sum split; not global rank/K/file'},indent=2))
