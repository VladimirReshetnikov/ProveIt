#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-axis-degree-generic-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='db66819e591f96214f7e3bac10855c96792ce71b9d7d58da7f655c486b64e019' and sha(p/'source-manifest.json')=='cfefd2cfb95a38a230922ef479de04faedbb667c3d644d6aaf32af4603a1079b'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14AxisGenericDegree';src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign17AxisDegreeScale'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('abbrev inner (z : ℤ) (correction rank : P) : P :=','(shift * shift) * ((shift * u z + correction) - rank) - u z','theorem inner_degree (z : ℤ) (hz : z ≠ 0) (correction rank : P)','(hc : correction.natDegree ≤ 2) (hr : rank.natDegree ≤ 4)','(inner z correction rank).natDegree = 8','u_degree z hz'):assert t in s
c=root/'reviews/nine-sharing-sign17-axis-degree-scale-terminal-independent/check.py';assert sha(c)=='3658632adea9397d9495fd66aac932e40f46368f3a5a5e53ea258626ccad5741';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "['outer_exit_code']==0" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic inner degree 8 under explicit correction/rank degree bounds and z nonzero; no actual axis binding or lower theorem'},indent=2))
