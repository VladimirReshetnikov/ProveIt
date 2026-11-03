from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-79-gauge-guard-obstruction');o=root/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='c25366a6bf76585bfc62f6f6e7c60dd5dc24682ae5f1d32c8b2af4040934e8d1';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='d0cbf2d2fd8666d9efeaeedd5de95ec62d5e48f803f174be53f674b7ede2ca24'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().splitlines()==["'Mask79GuardObstruction.guard_forces_zero' depends on axioms: [propext, Classical.choice, Quot.sound]","'Mask79GuardObstruction.moved_guard_iff' depends on axioms: [propext, Classical.choice, Quot.sound]"] and not (o/'stderr').read_text()
code=(root/'Mask79GuardObstruction.lean').read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['Mask79NaturalLiftV2'] and not re.search(r'\b(sorry|admit)\b',code);s=re.sub(r'\s+','',code)
assert '(hF:0<v1)' in s and '(v1+bpv*t)+(v2-qpv*bpv*t)<qpv' in s and 't=0∧v1+v2<qpv' in s and 'by_contraht' in s
p=Path('/tmp/mask79-naturallift-uaxz8axx/Mask79NaturalLiftV2.olean');assert str(p) in r['pins'] and sha(p)==r['pins'][str(p)]['sha256']
for b in range(10):
 for F in range(1,10):
  for C in range(15):
   for t in range(8):
    q=b+1;assert (F+b*t+max(C-q*b*t,0)<q)==(t==0 and F+C<q)
print('PASS: exact arbitrary IΣ₁ model semiring nonnegative-parameter guard iff, positive F, truncated subtraction, zero/nonzero case proof, direct lift pin and retained two axiom reports verified; finite sanity checks passed.')
