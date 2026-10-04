"""Report-only inert JSON to LaTeX tables; no trajectory or rule execution."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
RULES = ROOT / 'science/construction/RULES.json'
RECEIPT = ROOT / 'independent_audit/exact_algebra_receipt.json'
PINS = {RULES: '0e145aecc4f60685570c41be57d04905eab5b3bfa1a25b185d0b7bcf27e2f2db',
        RECEIPT: '4576156d03853c41c290173481f0bfe51e81c54ae470f70d9491e387b6b94cf8'}

def frac(value):
    f = Fraction(value)
    sign = '-' if f < 0 else ''
    f = abs(f)
    return sign + (str(f.numerator) if f.denominator == 1 else r'\frac{' + str(f.numerator) + '}{' + str(f.denominator) + '}')

def label(value):
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', value):
        raise ValueError('Unexpected label')
    return r'\texttt{' + value.replace('_', r'\_') + '}'

for path, expected in PINS.items():
    if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError('Input does not match frozen pin')

root = ROOT / 'assets'
root.mkdir(exist_ok=True)
outputs = [root / 'guards.tex', root / 'rules.tex']
if any(p.exists() or p.is_symlink() for p in outputs):
    raise FileExistsError('Table outputs must not exist')

data = json.loads(RECEIPT.read_text())
rows = sorted(data['distance_sorted'], key=lambda r:r[1])
if [r[1] for r in rows] != list(range(1,37)):
    raise ValueError('Guard numbering mismatch')
guard = [r'\begin{longtable}{@{}rlrrrr@{}}',
         r'\toprule Row & Block & $a$ & $b$ & $c$ & Distance squared\\\midrule\endfirsthead',
         r'\toprule Row & Block & $a$ & $b$ & $c$ & Distance squared\\\midrule\endhead']
for distance, number, name, coefficients in rows:
    if name[0] not in 'ABC' or len(coefficients) != 3:
        raise ValueError('Unexpected guard row')
    guard.append(str(number)+' & '+name[0]+' & '+ ' & '.join('$'+frac(v)+'$' for v in coefficients+[distance])+r' \\[3pt]')
guard += [r'\bottomrule', r'\end{longtable}']

rules=json.loads(RULES.read_text())
if rules['explicit_rule_count'] != 138 or len(rules['meta_signals']) != 169:
    raise ValueError('Count mismatch')
table = [r'\begingroup\small', r'\begin{longtable}{@{}rllllrr@{}}',
         r'\toprule $j$ & Phase & $Z_{\rm in}$ & $Z_{\rm out}$ & $Q_{\rm out}$ & $v_Q^-$ & $v_Q^+$\\\midrule\endfirsthead',
         r'\toprule $j$ & Phase & $Z_{\rm in}$ & $Z_{\rm out}$ & $Q_{\rm out}$ & $v_Q^-$ & $v_Q^+$\\\midrule\endhead']
for j,r in enumerate(rules['explicit_rules']):
    if r['index']!=j or r['input'][0] != f'Q{j}' or r['output'][0] != f'Q{(j+1)%138}':
        raise ValueError('Rule indexing mismatch')
    phase = r['primitive']
    if not re.fullmatch(r'[A-Za-z0-9_]+', phase):
        raise ValueError('Unexpected phase')
    phase=phase.replace('transfer_right','right').replace('transfer_left','left')
    table.append(f"{j} & {phase} & {label(r['marker_in'])} & {label(r['marker_out'])} & {label(r['output'][0])} & ${frac(r['messenger_in_speed'])}$ & ${frac(r['messenger_out_speed'])}$"+r' \\')
table += [r'\bottomrule',r'\end{longtable}',r'\endgroup',r'\subsection*{Temporary marker labels and their physical speeds}',
          r'\begin{longtable}{@{}lr@{}}',r'\toprule Label & Speed\\\midrule\endfirsthead',r'\toprule Label & Speed\\\midrule\endhead']
temporary=[s for s in rules['meta_signals'] if '_' in s['name']]
if len(temporary)!=27:
    raise ValueError('Temporary count mismatch')
for s in temporary:
    table.append(label(s['name'])+' & $'+frac(s['speed'])+r'$ \\[2pt]')
table += [r'\bottomrule',r'\end{longtable}']
for path, lines in zip(outputs,[guard,table]):
    with path.open('x',encoding='utf-8') as f:
        f.write('\n'.join(lines)+'\n')
print(json.dumps({str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in outputs},sort_keys=True))
