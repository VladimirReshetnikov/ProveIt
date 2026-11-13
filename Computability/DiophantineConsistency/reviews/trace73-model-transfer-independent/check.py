from pathlib import Path
from hashlib import sha256
import json,re
h=Path('research/trace73-model-transfer');o=h/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='37558ef64b593b2f8d5a13dd2cf53df0248d124406ac54101c71effcaeefe8ea';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(h/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='58fbf66066cf550957f7f24378dd943708b97750b26142164e224eaef214c930'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ('stdout','stderr'):assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().splitlines()==["'Trace73ModelTransfer.from75' depends on axioms: [propext, Classical.choice, Quot.sound]","'Trace73ModelTransfer.from73' depends on axioms: [propext, Classical.choice, Quot.sound]"] and not (o/'stderr').read_text()
code=(h/'Trace73ModelTransfer.lean').read_text();imports=re.findall(r'^import\s+(\S+)',code,re.M);assert imports==['Trace73Literal','DiophantineConsistency.ModelDifferenceRing','Foundation.FirstOrder.Arithmetic.IOpen.Basic'] and not re.search(r'\b(sorry|admit)\b',code);s=re.sub(r'\s+','',code)
for frag in ['(p:Fin4→ℕ)(v:Fin10→V)(m:V)','(hm:0<m)','(hcenter:(ι(v7):DiffRingV)=ιm+shiftpv)','value75(portsp)(castValv)=0','Trace73Literal.graph73(portsp)(castValw)=0','(p:Fin4→ℕ)(v:Fin10→V)(d:V)','(hd:shiftpv=ιd)','Trace73Literal.graph73(portsp)(castValv)=0','value75(portsp)(castValw)=0','letw:=Function.updatev7m','letw:=Function.updatev7(v7+d)']:assert frag in s,frag
paths=['/tmp/trace73-literal-1adlrevr','/tmp/trace73-center-r4z617bq','/tmp/trace73-model-caa17ucr/union','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
for n in imports+['Trace73CenterV2','DiophantineConsistency.TenPositiveTrace75']:
 p=next((Path(x)/(n.replace('.','/')+'.olean') for x in paths if (Path(x)/(n.replace('.','/')+'.olean')).is_file()),None);assert p;matching=[v for k,v in r['pins'].items() if Path(k).resolve()==p.resolve() and v['sha256']==sha(p)];assert matching,(n,p);print(n,str(p),sha(p))
print('PASS: same natural ports, exact center positive/shift lift assumptions, both update witnesses and positive zero conclusions; current first providers and receipt checked.')
