#!/usr/bin/env python3
"""Review sign15 pointwise zero assembly without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign15-zero-assembly-check';draft=root/'research/nine-sharing-sign15-zero-assembly-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='3b46c82746a3113d054a7b95d188e36dc4df2b0bec4e756fec22644e01fff46e' and sha(m)=='137ce9cfaa7c51dd0b38ad2f16a2750bb9f615e8b4e32923444c7a6bf811862b';rows=json.loads(m.read_text())['rows'];names=['Sign15ForwardBridge','Sign15ReverseBridge'];assert [r['module'].split('.')[-1] for r in rows]==names;text=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();text.append(s);assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 assert row['imports']==(['DiophantineConsistency.Sign15Transfer'+f'{j:02}' for j in range(6)] if i==0 else ['DiophantineConsistency.Sign15ForwardBridge'])
f,b=text;assert 'theorem forward' in f and '(hg : ι gap =' in f and 'Sign15Coordinate.d_zero' in f and 'theorem backward' in b and 'Sign15Coordinate.old_gap' in b
for gate in ('Dc2','tau','N0','Nt','Na','scaled_Ns'):assert 'Sign15Transfers.'+gate+'_eval' in f and 'Sign15Transfers.'+gate+'_eval' in b
r=run.read_text();assert "matches=[x for x in base['rows'] if x['module']==local]" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign15-transfers-terminal-independent/check.py';assert sha(check)=='ce27a2c48f7a212ee879be4c7910cc84cc178eb13847b1aa3a4c30a0ff9dd1e8';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(run),'stages':2,'scope':'conditional pointwise forward/reverse zero assembly; existential iff remains separate'},indent=2,sort_keys=True))
