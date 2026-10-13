"""StubFinal.lean: StubAll18 (heavy corpus theorems as axioms) + Proofs18Final + the new
bridge body + the new CompletionAudit section (whitelist widened by the stub axioms)."""
import re
from pathlib import Path
HERE = Path(__file__).resolve().parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
V = re.compile(r'(Proofs18Cover(Modulus|Density|Exponents)Fejer[A-Z][A-Z0-9]*|Proofs18CoverFejerHeadline[A-Z][A-Z0-9]*|Proofs18TightClassesFejer[A-Z][A-Z0-9]*|Proofs16PolynomialFejer[A-Z][A-Z0-9]*|Proofs18CoverFejerLowDegrees\d|Proofs18CoverFejerShortLengths\d|Proofs16SplitTwoTrack\w*|Proofs16UniformCoverTwoTight|Proofs18FejerEnvelopeBase[A-Z])$')
stub = (HERE / 'StubAll18.lean').read_text(encoding='utf8')
lines = stub.split('\n')
imports = [l for l in lines if l.startswith('import ') and not V.search(l.split()[1])]
imports += ['import GowersSzemeredi.Proofs18Final', 'import Lean.Util.CollectAxioms']
rest = '\n'.join(l for l in lines if not l.startswith('import '))
rest = rest[:rest.index('#print axioms')]
bridge = (GS / 'Proofs18CoverFejerAllDegrees.lean').read_text(encoding='utf8')
body = bridge[bridge.index('namespace LeanProofs.GowersSzemeredi'):]
audit = (GS / 'CompletionAudit.lean').read_text(encoding='utf8')
sec = audit[audit.index('-- The final route'):audit.index('-- The refutation is checked separately')]
STUB_AX = ('``LeanProofs.GowersSzemeredi.commonDiffPartitionBoundAt_of, '
           '``LeanProofs.GowersSzemeredi.multilinearPartitionBoundAt_explicit, '
           '``LeanProofs.GowersSzemeredi.section16RecurrenceProfileWith_explicit')
old = 'let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]'
assert old in sec
sec = sec.replace(old, old[:-1] + ', ' + STUB_AX + ']')
out = '\n'.join(imports) + '\n' + rest + '\n' + body + '\n' + sec
(HERE / 'StubFinal.lean').write_text(out, encoding='utf8', newline='\n')
print('wrote', len(out.splitlines()))
