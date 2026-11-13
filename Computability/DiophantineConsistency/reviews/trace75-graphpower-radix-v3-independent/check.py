#!/usr/bin/env python3
"""Check the pinned historical transitive provider reruns; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json
D=Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
cases=[('graphpower','Trace75GraphPower','graph_power','graphpower-attempt02','graphpower-attempt03','run-graphpower-v3.py','5704c79a5e8a267190a59ac245282eb119c7e3ea039d43cbc4b55dde1802d9a9'),('radixalignment','Trace75RadixAlignment','graph_radix_alignment','radixalignment-attempt01','radixalignment-attempt02','run-radixalignment-v3.py','ab373a05258ece9a1da30257e262cf84af2d02e5adbe727bee077babeefd93c2')]
for label,mod,th,old,new,runner,out in cases:
 a=P/'observations'/old;b=P/'observations'/new;x=json.loads((a/'terminal.json').read_text());y=json.loads((b/'terminal.json').read_text());src=P/(mod+'.lean');assert x['exit']==y['exit']==0 and x['reason'] is None and y['reason'] is None
 assert sha(P/runner)==y['runner_sha256'] and sha(src)==sha(a/'source.txt')==sha(b/'source.txt')==y['inputs'][str(src)]
 assert sha(Path(x['output_root'])/(mod+'.olean'))==x['object_sha256']==sha(Path(y['output_root'])/(mod+'.olean'))==y['object_sha256']==out
 for path,h in y['inputs'].items():assert sha(path)==h,path
 assert sha(b/'stdout')==y['stdout_sha256'] and sha(b/'stderr')==y['stderr_sha256'] and not (b/'stderr').read_text() and (b/'stdout').read_text()==f"'{mod}.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
 rel='DiophantineConsistency/ModelRatioBounds.olean';sel=next(Path(root)/rel for root in y['lean_path'].split(':') if (Path(root)/rel).is_file());assert str(sel) in y['inputs'] and sha(sel)==y['inputs'][str(sel)]=='fcf4152e49cb9a989bd9f8ba08259a26c646dfca18370b0c6e1ce7ebfb33b8a7'
 print(label,'first selected transitive',sel,'resolved',sel.resolve(),'sha',sha(sel),'object',out)
if True:
 graph=json.loads((P/'observations/graphpower-attempt03/terminal.json').read_text());radix=json.loads((P/'observations/radixalignment-attempt02/terminal.json').read_text());g=Path(graph['output_root'])/'Trace75GraphPower.olean';assert radix['inputs'][str(g)]==sha(g)==graph['object_sha256'];first=next(Path(q)/'Trace75GraphPower.olean' for q in radix['lean_path'].split(':') if (Path(q)/'Trace75GraphPower.olean').is_file());assert first.resolve()==g.resolve()
print('PASS v3 reruns, unchanged outputs, pinned post-hoc first-selected historical transitive and fresh graphpower provider; no Lean replay')
