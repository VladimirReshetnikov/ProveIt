"""Generate the report's numeric tables from checked diagnostic JSON."""
import argparse
import json
from pathlib import Path
from decimal import Decimal
ROOT=Path(__file__).resolve().parent

def sci(s):
    val=Decimal(s)
    mant,exponent=format(val,'.6E').split('E')
    return r'$'+mant+r'\times10^{'+str(int(exponent))+r'}$'

def tables(obj):
    diag=[r'\begin{table}[htbp]',r'\centering\small',
          r'\begin{tabular}{rrrrrr}',r'\toprule',
          r'$n$ & $V_n$ & $E_1(n)$ & $E_2(n)$ & $E_3(n)$ & $E_4(n)$ \\',r'\midrule']
    for row in obj['rows']:
        fields=[str(row['n']),format(Decimal(row['normalized']),'.12f')]
        fields += [format(Decimal(v),'.7f') for v in row['scaled_errors_after_J_terms'][1:]]
        diag.append(' & '.join(fields)+r' \\')
    diag += [r'\bottomrule',r'\end{tabular}',
             r'\caption{Finite 80-digit diagnostics, rounded for display. Each $E_J$ uses $J$ oscillatory terms and the scale in \eqref{eq:scalederror}.}',
             r'\label{tab:diag}',r'\end{table}']
    inv=[r'\begin{table}[htbp]',r'\centering',r'\begin{tabular}{rrr}',r'\toprule',
         r'$n$ & $t_1(a(n))-n$ & $t_4(a(n))-n$ \\',r'\midrule']
    for row in obj['inverse_offsets']:
        inv.append(' & '.join([str(row['n'])]+[sci(r['t_minus_n']) for r in row['offsets']])+r' \\')
    inv += [r'\bottomrule',r'\end{tabular}',
            r'\caption{Diagnostic smooth-inverse offsets at exact integer sequence levels. These are numerical observations, not certified interval enclosures.}',
            r'\label{tab:inverse}',r'\end{table}']
    return {'diagnostic_table.tex':'\n'.join(diag)+'\n','inverse_table.tex':'\n'.join(inv)+'\n'}

parser=argparse.ArgumentParser()
parser.add_argument('--check',action='store_true')
parser.add_argument('--output-dir',type=Path,default=ROOT.parent)
args=parser.parse_args()
source=args.output_dir/'Report211.tex'
text=source.read_text()
for name,content in tables(json.loads((ROOT/'diagnostics.json').read_text())).items():
    stem=name.removesuffix('.tex')
    begin='% BEGIN '+stem+'\n'
    end='% END '+stem
    if text.count(begin)!=1 or text.count(end)!=1:
        raise RuntimeError('Missing or duplicate table markers: '+stem)
    left, rest=text.split(begin)
    current, right=rest.split(end)
    if args.check:
        if current!=content:
            raise RuntimeError('Table mismatch: '+name)
    else:
        text=left+begin+content+end+right
if not args.check:
    source.write_text(text)
print('PASS: numeric table fields match diagnostics.json' if args.check else 'Updated numeric tables')
