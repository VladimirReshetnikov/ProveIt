from pathlib import Path
from hashlib import sha256
import json,re
h=Path('research/trace73-model-signs');o=h/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='e8f88707eddba98db80e9d5e7819321027e3db118dffc68faa2094127377750f';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(h/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='fc3a5776eb50bccdb99874e90fd09242432a6540dc4156ac5d30bd3a98b440f9'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ('stdout','stderr'):assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().splitlines()==[f"'Trace73ModelSigns.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in ['from75_of_bounds','from73_of_nonneg','shift_nonneg_of_B']] and not (o/'stderr').read_text()
code=(h/'Trace73ModelSigns.lean').read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['Trace73ModelTransfer'] and not re.search(r'\b(sorry|admit)\b',code);s=re.sub(r'\s+','',code)
for frag in ['(hnonneg:0≤shiftpv)','(hbound:shiftpv<ι(v7))','value75(portsp)(castValv)=0','Trace73Literal.graph73(portsp)(castValw)=0','Trace73Literal.graph73(portsp)(castValv)=0','value75(portsp)(castValw)=0','(hB:0≤(regs(portsp)(castValv)).B):0≤shiftpv','exactfrom75p v(v7-d)hvh mhchz'.replace(' ', ''),'exactfrom73pvdhvhdhz']:assert frag in s,frag
p=Path('/tmp/trace73-model-caa17ucr/Trace73ModelTransfer.olean');assert str(p) in r['pins'] and sha(p)==r['pins'][str(p)]['sha256']
print('PASS: exact 75-side nonnegative+strict bound, 73-side nonnegative shift and separately B≥0 sufficient condition verified with source/receipt/direct pin.')
