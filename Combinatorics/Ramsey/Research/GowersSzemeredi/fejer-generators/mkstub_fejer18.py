"""StubFejer18.lean: StubAll18 (heavy corpus theorems as axioms, the d+7 bridge inline)
plus the Fejér light modules and the body of Proofs18CoverFejerAllDegrees."""
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
stub = (HERE / 'StubAll18.lean').read_text(encoding='utf8')
bridge = (GS / 'Proofs18CoverFejerAllDegrees.lean').read_text(encoding='utf8')
lines = stub.split('\n')
imports = [l for l in lines if l.startswith('import ')]
rest = '\n'.join(l for l in lines if not l.startswith('import '))
cut = rest.index('#print axioms')
rest = rest[:cut]
extra = [l for l in bridge.split('\n') if l.startswith('import ') and 'Proofs18CoverSharperAllDegrees' not in l]
body = bridge[bridge.index('namespace LeanProofs.GowersSzemeredi'):]
names = re.findall(r'^theorem (\S+)', body, re.M)
prints = '\n'.join(f'#print axioms LeanProofs.GowersSzemeredi.{n}' for n in names)
out = '\n'.join(imports + extra) + '\n' + rest + '\n' + body + '\n' + prints + '\n'
(HERE / 'StubFejer18.lean').write_text(out, encoding='utf8', newline='\n')
print('wrote', len(out.splitlines()), 'lines;', len(names), 'theorems')
