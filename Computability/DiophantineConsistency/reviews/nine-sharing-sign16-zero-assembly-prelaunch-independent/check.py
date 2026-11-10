#!/usr/bin/env python3
"""Review sign16 pointwise zero assembly without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign16-zero-assembly-check';draft=root/'research/nine-sharing-sign16-zero-assembly-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='01265eed79e9573c5b29f762b5ad7c78a3a9786593b7e95f1c8447a6d2432ff0' and sha(m)=='7e23eefabf5c2d6204c9a7ccaed49988815fce67150155d41f839ec799b46b13';rows=json.loads(m.read_text())['rows'];names=['Sign16ForwardBridge','Sign16ReverseBridge'];assert [r['module'].split('.')[-1] for r in rows]==names;text=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();text.append(s);assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 assert row['imports']==(['DiophantineConsistency.Sign16Transfer'+f'{j:02}' for j in range(7)] if i==0 else ['DiophantineConsistency.Sign16ForwardBridge'])
f,b=text;assert 'theorem forward' in f and '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in f and '(hg : ι gap =' in f and 'Sign16Coordinate.d_zero' in f and 'theorem backward' in b and '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in b and 'Sign16Coordinate.old_gap' in b
for gate in ('Dc2','tau','N0','Nt','cTminusR','Na','scaled_Ns'):assert 'Sign16Transfers.'+gate+'_eval' in f and 'Sign16Transfers.'+gate+'_eval' in b
r=run.read_text();assert "matches=[x for x in base['rows'] if x['module']==local]" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign16-transfers-terminal-independent/check.py';assert sha(check)=='9d851c46a86e90d7e3edcba0867eebc17df4cd21c488b2a4195b03aa0a319971';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(run),'stages':2,'scope':'conditional pointwise forward/reverse zero assembly; existential iff remains separate'},indent=2,sort_keys=True))
