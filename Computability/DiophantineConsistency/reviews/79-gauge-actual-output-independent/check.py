from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-79-gauge-actual-output');o=root/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='26c29f80e8d171996c9a82e78e5526629d23cfe50c6d65af1fd55d57c85e6e6f';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='74ff4836864800cfd4c6720c005ec7263038ac79b814576c8885ea706c8e703a'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
assert r['pins']['/tmp/mask79-actual-f441d356/Mask79ActualRowsV3.olean']['sha256']=='99cb4d4e542ccef9de028afdd36b2d283c50129c48159a7454198a098cc31151'
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().strip()=="'Mask79ActualOutput.output_move' depends on axioms: [propext, Quot.sound]" and not (o/'stderr').read_text()
code=(root/'Mask79ActualOutput.lean').read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['Mask79ActualRowsV3'];assert not re.search(r'\b(sorry|admit)\b',code)
compact=re.sub(r'\s+','',code);assert '![v0,v1+s.b*t,v2-s.q*s.b*t,v3,v4,v5,v6,v7-(s.b*s.sq+1)*D*t,v8,v9]' in compact
assert 'theoremoutput_move(p:Fin4→ℤ)(v:Fin10→R)(t:R):' in compact and '(output79p).evalRing(movevst)=(output79p).evalRingv' in compact
for q in ['Mask79Carrier.preserve_rank_and_main','TenPositive79Mask.new_core','core_decompose','shared_move']:assert q in code
assert "rw [hrank, core_decompose, core_decompose, shared_move]" in code and 'exact hgauge.2' in code and 'exact hgauge.1' in code
print('PASS: actual output79 all-ring evaluator identity and exact three-slot gauge inspected; retained direct provider, source, output and axiom evidence checked. No positivity/guard theorem.')
