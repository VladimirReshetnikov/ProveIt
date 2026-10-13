"""Retire the variant chains in favour of the final route (Notes L.16-final).

usage: python -X utf8 retire.py [--apply]
Without --apply only prints what it would do.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean')
GS = LEAN / 'GowersSzemeredi'
V = re.compile(r'^(Proofs18Cover(Modulus|Density|Exponents)Fejer[A-Z][A-Z0-9]*|Proofs18CoverFejerHeadline[A-Z][A-Z0-9]*'
               r'|Proofs18TightClassesFejer[A-Z][A-Z0-9]*|Proofs16PolynomialFejer[A-Z][A-Z0-9]*'
               r'|Proofs18CoverFejerLowDegrees\d|Proofs18CoverFejerShortLengths\d|Proofs16SplitTwoTrack\w*'
               r'|Proofs16UniformCoverTwoTight|Proofs18FejerEnvelopeBase[A-Z])$')
NEW = ['Proofs18FinalClasses', 'Proofs18FinalStep', 'Proofs18FinalEnvelopes', 'Proofs18Final']
APPLY = '--apply' in sys.argv


def write(p, text):
    if APPLY:
        p.write_text(text, encoding='utf8', newline='\n')


facade = LEAN / 'GowersSzemeredi.lean'
ft = facade.read_text(encoding='utf8')
gone = [m for m in re.findall(r'^import GowersSzemeredi\.(\S+)\s*$', ft, re.M) if V.match(m)]
files = sorted(f.stem for f in GS.glob('*.lean') if V.match(f.stem))
print(len(gone), 'facade imports;', len(files), 'files')
assert set(gone) == set(files), (set(gone) ^ set(files))
# no remaining importer outside the retired set
for f in list(GS.glob('*.lean')) + [facade]:
    if f.stem in files or f.name == 'GowersSzemeredi.lean':
        continue
    for d in re.findall(r'^import GowersSzemeredi\.(\S+)', f.read_text(encoding='utf8'), re.M):
        if d in files and f.stem not in ('Proofs18CoverFejerAllDegrees', 'IntegerOriginalCorollaryFidelityAudit'):
            raise SystemExit(f'{f.name} still imports {d}')
lines = [l for l in ft.split('\n') if not (l.startswith('import GowersSzemeredi.') and l.split('.', 1)[1].strip() in files)]
last = max(i for i, l in enumerate(lines) if l.startswith('import '))
for m in reversed(NEW):
    if f'import GowersSzemeredi.{m}' not in lines:
        lines.insert(last + 1, f'import GowersSzemeredi.{m}')
write(facade, '\n'.join(lines))
total = 0
for m in files:
    total += (GS / f'{m}.lean').read_text(encoding='utf8').count('\n')
    if APPLY:
        (GS / f'{m}.lean').unlink()
print('deleted lines', total)

# bridge
new = GS / 'Proofs18CoverFejerAllDegrees.lean.new'
old = GS / 'Proofs18CoverFejerAllDegrees.lean'
print('bridge', old.read_text(encoding='utf8').count('\n'), '->', new.read_text(encoding='utf8').count('\n'))
if APPLY:
    new.replace(old)

# fidelity aggregator
fa = GS / 'IntegerOriginalCorollaryFidelityAudit.lean'
t = fa.read_text(encoding='utf8')
assert 'import GowersSzemeredi.Proofs16PolynomialFejerT3\n' in t
write(fa, t.replace('import GowersSzemeredi.Proofs16PolynomialFejerT3\n', 'import GowersSzemeredi.Proofs18FinalEnvelopes\n'))

# completion audit: replace the Fejér section
ca = GS / 'CompletionAudit.lean'
t = ca.read_text(encoding='utf8')
a = t.index('-- The Fejér route (Notes L.16e)')
end_marker = 'logInfo "Checked the Fejér-route strengthenings'
b = t.index('\n', t.index(end_marker)) + 1
sec = (HERE / 'audit_final_section.lean.txt').read_text(encoding='utf8')
write(ca, t[:a] + sec + t[b:])
print('audit', t.count('\n'), '->', (t[:a] + sec + t[b:]).count('\n'))
