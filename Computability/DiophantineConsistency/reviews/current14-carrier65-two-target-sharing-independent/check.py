#!/usr/bin/env python3
import gzip,hashlib,json,math,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier65-two-target-sharing';source=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();rec=json.loads((pkg/'result.json').read_bytes());ctl=json.loads((pkg/'control.json').read_bytes());assert sha(source)==rec['source_sha256']==ctl['source_sha256']=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(pkg/'screen.py')==rec['screen_sha256']==ctl['screen_sha256'];g=json.loads(source.read_bytes());rows=g['source'];assert len(rows)==65 and len(g['witnesses'])==14
ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(source.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];data=gzip.decompress(z);assert len(data)==m['raw_bytes'] and hashlib.sha256(data).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(data,'big')
P=tuple(rec['primes']);assert len(set(P))==3 and all(p>1 and all(p%d for d in range(2,math.isqrt(p)+1)) for p in P) and rec['samples_per_prime']==3 and rec['seed']==0x2C65
rng=random.Random(0x2C65);mods=[p for p in P for _ in range(3)];values={x:tuple(rng.randrange(1,p) for p in mods) for x in g['witnesses']};values.update({name:tuple(x%p for p in mods) for name,x in ports.items()});values.update({i:(i,)*len(mods) for i in range(5)})
for x,v in values.items():assert x==0 or all(v)
for name,op,a,b in rows:
 assert name not in values and a in values and b in values
 va,vb=values[a],values[b];values[name]=tuple((x+y if op=='+' else x-y if op=='-' else x*y)%p for x,y,p in zip(va,vb,mods));assert all(values[name])
counts=rec['counts'];assert not rec['candidates'] and not rec['control_mode'] and counts['target_queries']==sum(4*(23+i)-1 for i in range(65))==14235 and counts['shared_gate_forms']==87*88+87*87==15225 and counts['target_pairs']==340 and counts['tested_replacements']==560
c=ctl['candidates'];assert ctl['control_mode'] and any(x['targets']==['c','d'] and x['forms']==[['+','y'],['-','y']] and x['shared']==['+','x','z'] and x['live']==4 for x in c)
# Verify the positive control identities and single-target gate liveness independently.
for x in range(-3,4):
 for y in range(-3,4):
  for z in range(-3,4):assert (x+y)+z==(x+z)+y and (x-y)+z==(x+z)-y
text=(pkg/'screen.py').read_text();assert "[z for z in choices if z[0]<=i]" in text and "if availability[x]>i:continue" in text and "for j in targets[ix+1:]" in text and "if kind=='r-'" in text
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-integer-leaf-superopt-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'two source-ordered exact-target one-gate replacements via one common earlier alias/binary gate or new fixed leaf; no direct-target aliases/global bound'},indent=2))
