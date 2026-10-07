#!/usr/bin/env python3
"""Regenerate the article's small exact table from the checked result JSON."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def generate():
    data=json.loads((ROOT/'results'/'exact_checks.json').read_text())
    if data.get('status')!='pass':
        raise ValueError('Passing exact checks are required')
    rows=[r for r in data['Pruefer_quotient_cases'] if r['N']>=4]
    if len(rows)!=9:
        raise ValueError('Unexpected table row count')
    result=[r'\begin{center}',r'\begin{tabular}{rrrrrr}',r'\toprule',
            r'$N$ & $q$ & All & Identity & $J=0$ & $\classB$\\',r'\midrule']
    for row in rows:
        result.append('&'.join(str(row[k]) for k in ('N','q','classes','identity','J_zero','B'))+r'\\')
    result.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
    return '\n'.join(result)+'\n'


if __name__=='__main__':
    print(generate(),end='')
