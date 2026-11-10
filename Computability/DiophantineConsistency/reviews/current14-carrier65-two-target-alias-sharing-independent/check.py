#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-two-target-alias-sharing';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();rec=json.loads((p/'result.json').read_bytes());ctl=json.loads((p/'control.json').read_bytes());alias=json.loads((p/'alias-control.json').read_bytes());source=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert sha(source)==rec['source_sha256']==ctl['source_sha256']==alias['source_sha256']=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(p/'screen.py')==rec['screen_sha256']==ctl['screen_sha256']==alias['screen_sha256'];assert rec['primes']==ctl['primes']==alias['primes']==[1000000007,1000000009,998244353] and rec['samples_per_prime']==3 and rec['seed']==0x2C65 and not rec['candidates']
c=rec['counts'];assert c['target_queries']==sum(4*(23+i) for i in range(65))==14300 and c['shared_gate_forms']==87*88+87*87==15225 and c['target_pairs']==340 and c['tested_replacements']==655
assert ctl['control_mode']=='--control' and any(x['targets']==['c','d'] and x['forms']==[['+','y'],['-','y']] and x['shared']==['+','x','z'] and x['live']==4 for x in ctl['candidates'])
assert alias['control_mode']=='--alias-control' and any(x['targets']==['a','b'] and x['forms']==[['alias',None],['alias',None]] and x['shared']==['+','x','y'] and x['live']==4 for x in alias['candidates'])
s=(p/'screen.py').read_text()
for x in ("requirements.setdefault(t,[]).append((i,target,'alias',None))",'if availability[x]>i:continue','[z for z in choices if z[0]<=i]',"if kind=='alias':mapping[name]=fresh;return None",'x=resolve(x)',"[row[0],row[1],resolve(row[2]),resolve(row[3])]",'size=live(new,resolve(output))'):assert x in s
# Fresh shared gates precede the first target and can reference only earlier source nodes.
# Consequently neither alias points to a deleted target, so one-level resolution suffices.
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-two-target-sharing-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'two exact-target replacements with optional direct aliases and one shared earlier gate/leaf, modular screen only; no global bound'},indent=2))
