"""StubAuditFejer.lean: StubFejer18 plus the Fejér audit block of CompletionAudit.lean,
with the whitelist widened by the stub axioms (they stand for audited corpus theorems)."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
stub = (HERE / 'StubFejer18.lean').read_text(encoding='utf8')
stub = stub[:stub.index('#print axioms')]
audit = (GS / 'CompletionAudit.lean').read_text(encoding='utf8')
a = audit.index('-- The Fejér route (Notes L.16e)')
b = audit.index('-- The refutation is checked separately')
block = audit[a:b]
STUB_AX = ('``LeanProofs.GowersSzemeredi.commonDiffPartitionBoundAt_of, '
           '``LeanProofs.GowersSzemeredi.multilinearPartitionBoundAt_explicit, '
           '``LeanProofs.GowersSzemeredi.section16RecurrenceProfileWith_explicit')
old = 'let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]'
assert old in block
block = block.replace(old, 'let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound, ' + STUB_AX + ']')
out = stub + '\nimport Lean.Util.CollectAxioms\n' if False else stub
if 'import Lean.Util.CollectAxioms' not in out:
    first = out.index('\n', out.rindex('\nimport ') + 1)
    out = out[:first] + '\nimport Lean.Util.CollectAxioms' + out[first:]
out = out + '\n' + block
(HERE / 'StubAuditFejer.lean').write_text(out, encoding='utf8', newline='\n')
print('wrote', len(out.splitlines()))
