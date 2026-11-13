from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-79-gauge-natural-lift');o=root/'observations/attempt02'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='ca3c42e5f051686d8dc8b6dd81165d043d7253b242d0c8e206aa5e8440c56e09';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run-v2.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='097ebdc4b112f9c470bc75d51b48b6d5355046becd4702641cc46e5b75d509d5'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().splitlines()==["'Mask79NaturalLift.moved_positive' depends on axioms: [propext, Classical.choice, Quot.sound]","'Mask79NaturalLift.moved_lift' depends on axioms: [propext, Classical.choice, Quot.sound]"] and not (o/'stderr').read_text()
code=(root/'Mask79NaturalLiftV2.lean').read_text();imports=re.findall(r'^import\s+(\S+)',code,re.M);assert imports==['Mask79ModelBridgeV2','Mathlib.Tactic.FinCases'];compact=re.sub(r'\s+','',code)
assert '![v0,v1+bpv*t,v2-qpv*bpv*t,v3,v4,v5,v6,v7-(bpv*z+1)*factorpv*t,v8,v9]' in compact
for s in ['(hc:qpv*bpv*t<v2)','(hn:(bpv*z+1)*factorpv*t<v7)']:assert compact.count(s)==2,s
assert '(shared(integerPortsp)vv(rankTerm(integerPortsp)vv)).sq=ιz' in compact and 'movevv s' not in compact and 'movevv s' not in code
assert 'movevv s' not in compact and 'movevvs(ιt)=funj=>ι(movedpvztj)' in compact
assert '∀j,0<movedpvztj' in compact and not re.search(r'\b(sorry|admit)\b',code)
paths=['/tmp/mask79-modelbridge-_ei3xjhy','/tmp/mask79-output-cqfif459','/tmp/mask79-actual-f441d356','/tmp/mask79-ring-92upnp8s','/tmp/mask79-carrier-w290b5ah','/tmp/tenpositive-80graph-d2v79zbc','/tmp/direct90-ipra-join-b66u_qqo/lib','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
for n in imports:
 rel=n.replace('.','/')+'.olean';p=next((Path(x)/rel for x in paths if (Path(x)/rel).is_file()),None);assert p and str(p) in r['pins'];print(n,str(p),sha(p))
a=root/'observations/attempt01';f=json.loads((a/'terminal.json').read_text());assert f['status']=='FAILED' and sha(a/'stdout')==f['stdout_sha256'] and 'error' in (a/'stdout').read_text()
print('PASS: exact strict bounds twice, same row-square representation, truncated model move, positivity and exact lifted ring move, selected direct pins and rejected first attempt checked; no guard or witness existence.')
