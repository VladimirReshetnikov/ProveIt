#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-sentinel-collision-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='3ab6c6765b87d1799d624593570b4ba566ef4863fd1cc384059793e29682c010' and sha(p/'source-manifest.json')=='23365ab2cb20d29a28173fa5ec51fe03ce4879f559a6a070c7c89514a9f8bc59';e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KSentinelCollision.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KSentinelCollision' and e['imports']==['DiophantineConsistency.Sign17KRadixReversal'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='280509d899306201fc9e6491d5c2840d29994cef3a5b878d6c53f51dc407a24e' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('theorem shifted_reversed (r n shift : ℕ)', 'theorem shifted_986 (r : ℕ) (v : Fin 986 → ℕ)', 'r ^ (1005 - i.val)', 'theorem middle_sentinel (r : ℕ) (v : Fin 986 → ℕ)', 'i = ⟨984, by decide⟩', '+ r ^ 1004'):assert t in s
assert 20+984==1004 and 985-984==1 and all(20+(986-(i+1))==1005-i for i in range(986))
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-radix-reversal-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-radix-reversal-check/attempt01/state.json').read_text());assert prior['status']=='PASS';obj=Path('/tmp/nine-sharing-sign17-k-radix-reversal-20261110/lib/DiophantineConsistency/Sign17KRadixReversal.olean');assert sha(obj)==prior['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic shifted reversal and middle-sentinel algebra only, no K/digit bounds/file theorem'},indent=2))
