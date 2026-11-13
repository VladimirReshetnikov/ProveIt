#!/usr/bin/env python3
"""Review sign14 pointwise zero assembly without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-zero-assembly-check';draft=root/'research/nine-sharing-sign14-zero-assembly-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='5f272501c5dedab03e0f9d7008befa7ccce853148e3f0185b7af09eb0678d978' and sha(m)=='17a01bce727b7712a2c843172fffc85f2cc7b877f25983f1202e72f092e6b157';rows=json.loads(m.read_text())['rows'];names=['Sign14ForwardBridge','Sign14ReverseBridge'];assert [r['module'].split('.')[-1] for r in rows]==names;text=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();text.append(s);assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 assert row['imports']==(['DiophantineConsistency.Sign14Transfer'+f'{j:02}' for j in range(5)] if i==0 else ['DiophantineConsistency.Sign14ForwardBridge'])
f,b=text;assert 'theorem forward' in f and '(hg : ι gap =' in f and 'Sign14Coordinate.d_zero' in f and 'theorem backward' in b and 'Sign14Coordinate.old_gap' in b
for gate in ('Dc2','N0','Nt','Na','scaled_Ns'):assert 'Sign14Transfers.'+gate+'_eval' in f and 'Sign14Transfers.'+gate+'_eval' in b
r=run.read_text();assert "matches=[x for x in base['rows'] if x['module']==local]" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign14-transfers-terminal-independent/check.py';assert sha(check)=='9639187b1f954cc6b468271b8f94d2764290e0cbaccda32208d8207e38f2c4cf';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(run),'stages':2,'scope':'conditional pointwise forward/reverse zero assembly; existential iff remains separate'},indent=2,sort_keys=True))
