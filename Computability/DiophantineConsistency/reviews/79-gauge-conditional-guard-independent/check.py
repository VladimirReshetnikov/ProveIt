from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-79-gauge-conditional-guard');o=root/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='4be1ab63ed7a294be970af56d39e71b4f58edd59edeada4d721382ee69e54af5';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='9d5e09a0151470b62f7bc81451f7fb3e110faa892e27e90720693c064c6aecc1'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().splitlines()==["'Mask79ConditionalGuard.square_represented' depends on axioms: [propext, Classical.choice, Quot.sound]","'Mask79ConditionalGuard.guarded_zero_of_parameter' depends on axioms: [propext, Classical.choice, Quot.sound]"] and not (o/'stderr').read_text()
code=(root/'Mask79ConditionalGuard.lean').read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['Mask79NaturalLiftV2'] and not re.search(r'\b(sorry|admit)\b',code);s=re.sub(r'\s+','',code)
for frag in ['∃z:V,letvv:=funj=>ι(vj)','(shared(integerPortsp)vv(rankTerm(integerPortsp)vv)).sq=ιz','(hc:qpv*bpv*t<v2)','(hn:(bpv*z+1)*factorpv*t<v7)','(hg:(v1+bpv*t)+(v2-qpv*bpv*t)<qpv)','(hz:InternalZero(output79(integerPortsp))v)','∃w:Fin10→V,(∀j,0<wj)∧w1+w2<qpw∧InternalZero(output79(integerPortsp))w','moved_positivepvzthvhchn','moved_liftpvzths qhchn'.replace(' ', '')]:assert frag in s,frag
p=Path('/tmp/mask79-naturallift-uaxz8axx/Mask79NaturalLiftV2.olean');assert str(p) in r['pins'] and sha(p)==r['pins'][str(p)]['sha256']
print('PASS: arbitrary-model shared square representation and conditional positive guarded InternalZero using same supplied z,t and three explicit inequalities; direct lift pin/logs verified; no parameter existence.')
