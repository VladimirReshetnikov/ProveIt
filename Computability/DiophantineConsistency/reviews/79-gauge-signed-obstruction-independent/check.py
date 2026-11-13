from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-79-gauge-signed-obstruction');o=root/'observations/attempt02'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='a8d7a24ce3c643e4655e79353f9bd714bc1e1798c75a08661b8c5219a899cdd7';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run-v2.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='d264bf32ee4a0ea5c4ecb8aa716cd666ce4a7d61c2f71af400bdfab66c278f66'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().strip()=="'Mask79SignedObstruction.no_guarded_lift' depends on axioms: [propext, Classical.choice, Quot.sound]" and not (o/'stderr').read_text()
code=(root/'Mask79SignedObstructionV2.lean').read_text();imports=re.findall(r'^import\s+(\S+)',code,re.M);assert imports==['Mask79ModelBridgeV2','Mask79NegativeObstruction'] and not re.search(r'\b(sorry|admit)\b',code);s=re.sub(r'\s+','',code)
for frag in ['(v w:Fin10→V)'.replace(' ',''),'(t:DiffRingV)','(hFpos:0<v1)','(hunguarded:qpv≤v1+v2)','movevvst=funj=>ι(wj)','¬w1+w2<qpw','rcasesnonneg_or_nonpostwith','exactno_negative_guardpvuhboundhunguardedhguard']:assert frag in s,frag
paths=['/tmp/mask79-negobstruction-131xhpwn','/tmp/mask79-naturallift-uaxz8axx','/tmp/mask79-modelbridge-_ei3xjhy','/tmp/mask79-output-cqfif459','/tmp/mask79-actual-f441d356','/tmp/mask79-ring-92upnp8s','/tmp/mask79-carrier-w290b5ah','/tmp/tenpositive-80graph-d2v79zbc','/tmp/direct90-ipra-join-b66u_qqo/lib','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
for n in imports:
 p=next((Path(x)/(n.replace('.','/')+'.olean') for x in paths if (Path(x)/(n.replace('.','/')+'.olean')).is_file()),None);assert p and str(p) in r['pins'] and sha(p)==r['pins'][str(p)]['sha256'];print(n,str(p),sha(p))
a=root/'observations/attempt01';f=json.loads((a/'terminal.json').read_text());assert f['status']=='FAILED' and sha(a/'stdout')==f['stdout_sha256'] and 'error' in (a/'stdout').read_text()
print('PASS: arbitrary difference-ring parameter, exact whole-valuation lift, positive F and unguarded premise, signed branch proof and direct pin/failed attempt verified; no graph-zero premise or inequivalence claim.')
