#!/usr/bin/env python3
"""Inspect source delta and author receipt for generic variable growth; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'PellVariableGrowth.lean';o=P/'observations/variablegeneric-attempt01';t=json.loads((o/'terminal.json').read_text());root=Path(t['output_root'])
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None and sha(P/'run-variablegeneric.py')==t['runner_sha256'];assert sha(s)==sha(o/'source.txt')==sha(root/s.name)==t['inputs'][str(s)]=='1feae7f7debc2ee2812b1ca6c3380e25479f5c838978dcbf043123b4d9642c52';assert sha(root/'PellVariableGrowth.olean')==t['object_sha256']=='4f082f68b44ec02452f69a012f104ce82debbc46806f9fd83e2d5ad70fdf59f8'
old=D/'research/pell-variable-growth-prototype/PellVariableGrowth.lean';v=old.read_text();assert v.count('import Direct80ProjectionPell\n')==1 and v.replace('import Direct80ProjectionPell\n','import DiophantineConsistency.ArithmeticPellPowerRecovery\n',1)==s.read_text()
for path,h in t['inputs'].items():assert sha(path)==h,path
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'] and not (o/'stderr').read_text()
expected='\n'.join(f"'TenPositivePellVariableGrowth.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in ('paired_comparison','paired_comparison_strict'))
assert (o/'stdout').read_text().strip()==expected and not re.search(r'\b(?:sorry|admit)\b',s.read_text())
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['DiophantineConsistency.ArithmeticPellPowerRecovery','DiophantineConsistency.ArithmeticPow']
for name in imports:
 rel=name.replace('.','/')+'.olean';path=next((Path(x)/rel for x in t['lean_path'].split(':') if (Path(x)/rel).is_file()),None);assert path and any(Path(q).resolve()==path.resolve() and h==sha(path) for q,h in t['inputs'].items()),name
 print(name,path,path.resolve(),sha(path))
print('PASS exact first-import-only delta, two reports, selected direct pins; no Lean replay')
