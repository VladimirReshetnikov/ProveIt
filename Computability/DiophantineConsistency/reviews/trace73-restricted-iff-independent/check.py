from pathlib import Path
from hashlib import sha256
import json,re
h=Path('research/trace73-restricted-iff');o=h/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='08076e907921b80714a26b6bd084c9c9317b0b4ca0f7ca43b8a0e356dbdbbfc0';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(h/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='f328387a531b858239b7ebb452c9b50535417051b603910f3822f9f63659fe45'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ('stdout','stderr'):assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text()=="'Trace73RestrictedIff.restricted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
code=(h/'Trace73RestrictedIff.lean').read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['Trace73ModelSigns'] and not re.search(r'\b(sorry|admit)\b',code);s=re.sub(r'\s+','',code)
for x in ['(∃v:Fin10→V,(∀j,0<vj)∧value75(portsp)(castValv)=0∧0≤shiftpv∧shiftpv<ι(v7))↔','(∃v:Fin10→V,(∀j,0<vj)∧Trace73Literal.graph73(portsp)(castValv)=0∧0≤shiftpv)','letw:=Function.updatev7(v7-d)','letw:=Function.updatev7(v7+d)','Trace73Literal.parent_substitution','shift_update']:assert x in s,x
p=Path('/tmp/trace73-signs-7edju0w1/Trace73ModelSigns.olean');assert str(p) in r['pins'] and sha(p)==r['pins'][str(p)]['sha256']
print('PASS: exact restricted both-existential iff, same ports and witness-side shift bounds, explicit model update witnesses and selected direct pin/receipt checked; no unrestricted equivalence.')
