#!/usr/bin/env python3
"""Inspect weighted projection and generic product estimate receipts, without Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
cases=[('Trace75Projection','projection-attempt01','run-projection.py','70d7b2a63f9f38da269fe04fbc1d23af4a2f7c50d43ec0221ff4bbc385eb4c85','8404795f081ea826e14cdb2bce21fa985977c760d1b0c08fe8e2148019ef9400','graph_projection_divisibility',['Trace75CarrierBound'],['Trace75Residue','Trace75Adjacent','Trace75Factors','DiophantineConsistency.TenPositiveTrace75']),('Trace75ProductPower','productpower-attempt01','run-productpower.py','7976e3060f14630f879ee8c677773b5e655ece5b5d282e880b1238a997add1a1','2999b26c4638f4d192f3a13784f1da2dd88e6c67f67b3ecbc3c21884dbeeb35e','whole_product_lt_power',['DiophantineConsistency.ArithmeticPellPowerRecovery','DiophantineConsistency.ArithmeticPow'],[])]
for mod,attempt,runner,source,obj,thm,imports,near in cases:
 s=P/(mod+'.lean');o=P/'observations'/attempt;t=json.loads((o/'terminal.json').read_text());root=Path(t['output_root']);assert t['exit']==0 and t['reason'] is None
 assert sha(P/runner)==t['runner_sha256'] and sha(s)==sha(o/'source.txt')==sha(root/s.name)==t['inputs'][str(s)]==source and sha(root/(mod+'.olean'))==t['object_sha256']==obj
 for path,h in t['inputs'].items():assert sha(path)==h,path
 assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'] and not (o/'stderr').read_text()
 assert ' '.join((o/'stdout').read_text().split())==f"'{mod}.{thm}' depends on axioms: [propext, Classical.choice, Quot.sound]"
 assert not re.search(r'\b(?:sorry|admit)\b',s.read_text()) and re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M)==imports
 for name in imports+near:
  rel=name.replace('.','/')+'.olean';path=next((Path(x)/rel for x in t['lean_path'].split(':') if (Path(x)/rel).is_file()),None);assert path and any(Path(q).resolve()==path.resolve() and h==sha(path) for q,h in t['inputs'].items()),name
  print(mod,name,path,path.resolve(),sha(path))
print('PASS source/objects/logs and post-hoc selected pinned direct/nearby providers; no Lean replay')
