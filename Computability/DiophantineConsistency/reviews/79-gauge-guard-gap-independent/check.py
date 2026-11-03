from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-79-gauge-guard-gap');o=root/'observations/attempt02'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='013b809b03af6ffe27a5c72b8c45b1a09d1488e2faa7d3a71e3691794173da37';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run-v2.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='e93cbe358d8ff862ada539b1b1b5b2c58bb50862b75ef6794f6851ab110d424f'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().splitlines()==["'Mask79GuardGap.guard_from_gap' depends on axioms: [propext, Classical.choice, Quot.sound]","'Mask79GuardGap.guarded_zero_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound]"] and not (o/'stderr').read_text()
code=(root/'Mask79GuardGapV2.lean').read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['Mask79ConditionalGuard'] and not re.search(r'\b(sorry|admit)\b',code);s=re.sub(r'\s+','',code)
for f in ['(hc:qpv*bpv*t<v2)','(hg:v1+v2<qpv+bpv*bpv*t)','(hn:(bpv*z+1)*factorpv*t<v7)','guarded_zero_of_parameterpvzthvhsqhchn(guard_from_gappvt hchg)hz'.replace(' ', '')]:assert f in s,f
p=Path('/tmp/mask79-condguard-u1lbyzjf/Mask79ConditionalGuard.olean');assert str(p) in r['pins'] and sha(p)==r['pins'][str(p)]['sha256']
a=root/'observations/attempt01';f=json.loads((a/'terminal.json').read_text());assert f['status']=='FAILED' and sha(a/'stdout')==f['stdout_sha256'] and 'error' in (a/'stdout').read_text()
for b in range(6):
 for F in range(5):
  for C in range(15):
   for t in range(5):
    q=b+1
    if q*b*t<C and F+C<q+b*b*t:assert F+b*t+max(C-q*b*t,0)<q
print('PASS: guard-gap inequality, explicit hc/hn/hsq/supplied t, same moved witness and zero, direct provider and rejected attempt checked; no parameter existence.')
