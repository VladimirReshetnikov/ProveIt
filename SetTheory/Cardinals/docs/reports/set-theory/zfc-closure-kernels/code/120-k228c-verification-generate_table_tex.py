#!/usr/bin/env python3
"""Generate the complete canonical table appendix from the literal machine."""
from pathlib import Path
import argparse
from table_reconstruction import parse, validate, require, PINS, sha

def render(table):
    blocks = []
    for base in (0, 114):
        text = [r'\clearpage', r'\subsection*{States ' + str(base) + '--' + str(base+113) + '}',
                r'\begin{center}\small', r'\setlength{\tabcolsep}{8pt}',
                r'\renewcommand{\arraystretch}{1.16}',
                r'\begin{tabular}{rll@{\hspace{9mm}}rll@{\hspace{9mm}}rll}', r'\toprule',
                r'$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 \\', r'\midrule']
        for row in range(38):
            fields = []
            for group in range(3):
                q = base + row + 38 * group
                fields.append(str(q))
                for b in (0, 1):
                    w, d, z = table[q, b]
                    fields.append(r'\texttt{' + f'{w}{"R" if d==1 else "L"}{z}' + '}')
            text.append(' & '.join(fields) + r' \\')
        text += [r'\bottomrule', r'\end{tabular}', r'\end{center}',
                 r'\noindent Each entry is write, direction, next state. State 228 is the unique halt label.']
        blocks.append('\n'.join(text))
    return '\n\n'.join(blocks) + '\n'

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--machine',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    raw=a.machine.read_bytes();require(sha(raw)==PINS['canonical'],'Wrong canonical table')
    table,start=parse(raw);validate(table,start,228,228)
    a.output.write_text(render(table));print('Generated complete appendix: 228 states, 456 transitions.')

if __name__=='__main__':main()
