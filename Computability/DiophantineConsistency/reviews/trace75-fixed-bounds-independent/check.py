#!/usr/bin/env python3
"""Check generic fixed symbolic bounds author receipt, no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75FixedBounds.lean';o=P/'observations/fixedbounds-attempt01';t=json.loads((o/'terminal.json').read_text());root=Path(t['output_root'])
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None and sha(P/'run-fixedbounds.py')==t['runner_sha256'];assert sha(s)==sha(o/'source.txt')==sha(root/s.name)==t['inputs'][str(s)]=='f23c2b78bbcbc083a5e15bd1deada0758e5a2dd9e8113c758a91df90a8a27d68' and sha(root/'Trace75FixedBounds.olean')==t['object_sha256']=='036b410cf7f1242e45a829413b019742c56af2c480ded871ce88c2ef3f76e822'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'] and not (o/'stderr').read_text();expected='\n'.join(f"'Trace75FixedBounds.{x}' depends on axioms: [propext, Classical.choice, Quot.sound]" for x in ('beta_ge_31','fixed_bounds'))+'\n';assert (o/'stdout').read_text()==expected
text=s.read_text();imports=re.findall(r'^import\s+([\w.]+)\s*$',text,re.M);assert imports==['DiophantineConsistency.CompactFixedBeta','DiophantineConsistency.CompactSymbolicPorts'] and not re.search(r'\b(?:sorry|admit)\b',text)
for name in imports+['DiophantineConsistency.ModelRatioBounds']:
 rel=name.replace('.','/')+'.olean';p=next((Path(x)/rel for x in t['lean_path'].split(':') if (Path(x)/rel).is_file()),None);assert p and any(Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),name
 print(name,p,p.resolve(),sha(p))
print('PASS two source/log reports and post-hoc selected pinned providers; no Lean replay')
