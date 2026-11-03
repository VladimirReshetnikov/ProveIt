from pathlib import Path
from hashlib import sha256
import json,re
h=Path('research/trace73-reverse-carrier-center');o=h/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='81fc041a2311ff09b3fbb33275a8899cf32c24833b33b22e68bca821d5e47458';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(h/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='689dda948bf6741250f7c27fd581933b417bda950e41f18b0b8ea8e5e05c0695'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ('stdout','stderr'):assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text()=="'Trace73ReverseCenter.positive_carrier_center' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
code=(h/'Trace73ReverseCenter.lean').read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['ReverseCarrier','TraceCenterPositiveV2'] and not re.search(r'\b(sorry|admit)\b',code);s=re.sub(r'\s+','',code)
for frag in ['(hK:Kpos=H*kappa)','(htau:0<tau)','(hy:0<y)','(hf:kappa<f)','∃n:V,0<n∧0<n-u*u*(b*t)∧','n+kappa=tau*f*y+u*u*(b*t)+t+rho∧','⟨n,hn,hbalance,hcarrier⟩','TraceCenterPositive.center_positivebt rhokappataufy unhtauhyhfhbalance'.replace(' ', '')]:assert frag in s,frag
for p in ['/tmp/reverse-carrier-fr1w8a_6/ReverseCarrier.olean','/tmp/trace-centerpositive-0_fb28_g/TraceCenterPositiveV2.olean']:assert p in r['pins'] and sha(p)==r['pins'][p]['sha256']
print('PASS: same scalar n and exact K=H*kappa, tau/y positivity, kappa<f, balance and difference-ring carrier conclusion; both provider pins and receipt checked.')
