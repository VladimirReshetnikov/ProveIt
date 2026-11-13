#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-axis-na-generic-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d2638d3316bf3629403cf1afa9a8773afeedbcbfe95a6f541bd332ba8d3c6908' and sha(p/'source-manifest.json')=='5623e16821dafd06773fdabde1c99801c46c2c1aaeb9ddeaacdc6301ea14979a'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14AxisGenericNaDegree';src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14AxisGenericDegree'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('abbrev row (z : ℤ) (correction rank : P) : P :=','theorem row_degree (z : ℤ) (hz : z ≠ 0) (correction rank : P)','(hc : correction.natDegree ≤ 2) (hr : rank.natDegree ≤ 4)','(row z correction rank).natDegree = 62','inner_degree z hz correction rank hc hr','scale_degree z hz'):assert t in s
c=root/'reviews/nine-sharing-sign14-axis-degree-generic-terminal-independent/check.py';assert sha(c)=='d8e7df010a2d5f921a22ed77c6d2d67bb89908ddae4796215dff4ac339ad3996';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "['author_observed_numeric_outer_exit']==0" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic Na degree 62 under explicit correction/rank degree bounds and z nonzero; no actual axis binding or lower theorem'},indent=2))
