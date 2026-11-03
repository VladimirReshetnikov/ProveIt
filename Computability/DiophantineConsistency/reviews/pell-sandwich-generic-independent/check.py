#!/usr/bin/env python3
"""Review explicit import additions and author sandwich receipts; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
cases=[('PellScaledSandwich','sandwichgeneric-attempt02','run-sandwichgeneric-v2.py','d86fd2d262fc8541e37f61462fdffbac082e0455a8e9168c3102df48b5f55778','0c172072f014a60e7ba1548cf2762232d2c86c3e1a95380e76d46879902feea6',['lower_of_gap','shifted_coefficient'],D/'research/pell-scaled-sandwich-prototype/PellScaledSandwich.lean',['PellVariableGrowth','DiophantineConsistency.ArithmeticPellPowerRecovery','DiophantineConsistency.ArithmeticPow','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticHalfBinomialSandwich']),('PellScaledUpper','uppergeneric-attempt01','run-uppergeneric.py','aca2f6d4710ccc0d818b48708d941555ff2ac275f3caf2ef95b369dcb7ff646e','ffaea0b89a05df089d988423ecffac9614131bd4f3e660863c91f03487e6b0f9',['shifted_upper_coefficient','upper_of_bounds'],D/'research/pell-scaled-sandwich-upper-prototype/PellScaledUpper.lean',['PellScaledSandwich','PellVariableGrowth','DiophantineConsistency.ArithmeticPellPowerRecovery','DiophantineConsistency.ArithmeticPow','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticHalfBinomialSandwich'])]
for mod,attempt,run,srcsha,objsha,names,old,imports in cases:
 s=P/(mod+'.lean');o=P/'observations'/attempt;t=json.loads((o/'terminal.json').read_text());root=Path(t['output_root']);assert t['exit']==0 and t['reason'] is None
 assert sha(P/run)==t['runner_sha256'] and sha(s)==sha(o/'source.txt')==sha(root/s.name)==t['inputs'][str(s)]==srcsha and sha(root/(mod+'.olean'))==t['object_sha256']==objsha
 for path,h in t['inputs'].items():assert sha(path)==h,path
 assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'] and not (o/'stderr').read_text()
 ns='TenPositive'+mod;expected='\n'.join(f"'{ns}.{x}' depends on axioms: [propext, Classical.choice, Quot.sound]" for x in names)+'\n';assert (o/'stdout').read_text()==expected
 text=s.read_text();assert not re.search(r'\b(?:sorry|admit)\b',text);newimports=re.findall(r'^import\s+([\w.]+)\s*$',text,re.M);oldimports=re.findall(r'^import\s+([\w.]+)\s*$',old.read_text(),re.M);assert newimports==imports
 strip=lambda z:re.sub(r'^import\s+[\w.]+\n','',z,flags=re.M)
 assert strip(text)==strip(old.read_text()) and all(n in newimports for n in oldimports)
 for name in imports+['DiophantineConsistency.ModelRatioBounds']:
  rel=name.replace('.','/')+'.olean';p=next((Path(x)/rel for x in t['lean_path'].split(':') if (Path(x)/rel).is_file()),None);assert p and any(Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),name
  print(mod,name,p,p.resolve(),sha(p))
bad=P/'observations/sandwichgeneric-attempt01';bt=json.loads((bad/'terminal.json').read_text());assert bt['exit']!=0 and 'unknown namespace' in (bad/'stdout').read_text()
print('PASS exact import-only additions, two generic theorem pairs, direct and old transitive pins; no Lean replay')
