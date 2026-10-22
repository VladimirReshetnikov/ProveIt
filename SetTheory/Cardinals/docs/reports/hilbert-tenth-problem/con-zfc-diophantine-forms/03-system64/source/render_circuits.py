#!/usr/bin/env python3
"""Generate literal LaTeX gate tables from the delivered inert JSON circuits."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
NAMES = {
    'Jrep': 'J', 'F': 'F', 'alpha': r'\alpha',
    'transport_quotient': 't', 'f': 'f', 'h': 'h', 'i': 'i',
    'auxiliary_quotient': 'T', 's': 's', 'w': 'w',
    'tau_root': r'\tau', 'eta': r'\eta', 'zeta': r'\zeta',
    'y_aux': 'y', 'Z': 'Z', 'gamma': r'\gamma',
    'Bm1': '(B-1)', 'Kconstant': 'K', 'twice_cell_bits': '2d',
    'MC': 'M_C', 'MF': 'M_F', 'marker_constant': 'W_*',
}

def render(packet, dest, label):
    names = dict(NAMES)
    lines = [r'\begin{longtable}{r@{\quad}l@{\hspace{16mm}}r@{\quad}l}',
             r'\caption{' + label + r'}\\',
             r'\toprule Gate & Polynomial abbreviation & Gate & Polynomial abbreviation \\ \midrule',
             r'\endfirsthead',
             r'\toprule Gate & Abbreviation (continued) & Gate & Abbreviation (continued) \\ \midrule',
             r'\endhead', r'\bottomrule\endfoot']
    entries = []
    for number, (name, op, lhs, rhs) in enumerate(packet['source'], 1):
        def term(x):
            return names[x] if isinstance(x, str) else str(x)
        symbol = r'\cdot' if op == '*' else op
        target = r'r_{' + str(number) + '}'
        entries.append(str(number) + ' & $' + target + '=' + term(lhs) + ' ' + symbol + ' ' + term(rhs) + '$')
        names[name] = target
    half = (len(entries)+1)//2
    for j in range(half):
        right = entries[j+half] if j+half < len(entries) else ' & '
        lines.append(entries[j] + ' & ' + right + r' \\')
    lines.append(r'\end{longtable}')
    if 'output' in packet:
        lines.append(r'The output polynomial is $' + names[packet['output']] + '$.')
    else:
        pairs = []
        for lhs, rhs in packet['comparisons']:
            a = names[lhs] if isinstance(lhs, str) else str(lhs)
            b = names[rhs] if isinstance(rhs, str) else str(rhs)
            pairs.append(a + '=' + b)
        lines.append(r'The seven comparisons are $' + r',\ '.join(pairs) + '$.')
    dest.write_text('\n'.join(lines) + '\n')

def main():
    variants = json.loads((ROOT/'artifacts/fixed_marker_variants.json').read_text())
    systems = json.loads((ROOT/'artifacts/fixed_marker_systems.json').read_text())
    render(variants['fixed_marker82'], ROOT/'artifacts/circuit_82.tex',
           'The exact 82-operation circuit for $P_{15}$.')
    render(systems['fixed_marker76_system'], ROOT/'artifacts/circuit_64.tex',
           'The exact 64-operation circuit for the seven comparisons.')
    print('Generated both literal circuit tables.')

if __name__ == '__main__':
    main()
