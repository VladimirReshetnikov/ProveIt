#!/usr/bin/env python3
"""Generate the LaTeX coverage ledger from claims/coverage.csv."""
from __future__ import annotations
import csv
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CSV = ROOT / 'claims' / 'coverage.csv'
OUT = ROOT / 'claims' / 'coverage_table.tex'

ASCII_ESC = {
    '&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#',
    '_': r'\_\allowbreak{}',
    '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}',
    '^': r'\textasciicircum{}\allowbreak{}',
    '/': r'\slash{}', '=': r'=\allowbreak{}',
    '\\': r'\textbackslash{}',
}
UNICODE = {
    '§': r'\S{}', '–': '--', '—': '---', '−': r'$-$',
    '≤': r'$\le$', '≥': r'$\ge$', '≠': r'$\ne$',
    '∞': r'$\infty$', 'π': r'$\pi$', 'α': r'$\alpha$',
    'β': r'$\beta$', 'γ': r'$\gamma$', 'δ': r'$\delta$',
    'η': r'$\eta$', 'ε': r'$\epsilon$', 'ν': r'$\nu$',
    'ρ': r'$\rho$', 'σ': r'$\sigma$', 'ω': r'$\omega$',
    'Φ': r'$\Phi$', 'Γ': r'$\Gamma$', '√': r'$\sqrt{\,}$',
    '∫': r'$\int$', '→': r'$\to$', '↦': r'$\mapsto$',
    '∈': r'$\in$', '′': r'$\prime$', '²': r'$^2$',
    '₀': r'$_0$', '₁': r'$_1$', '₂': r'$_2$', '₃': r'$_3$',
    '₄': r'$_4$', '₅': r'$_5$', '₆': r'$_6$', '₇': r'$_7$',
    '₈': r'$_8$', '₉': r'$_9$', '“': '``', '”': "''",
    '’': "'", 'é': r"\'e", 'É': r"\'E", 'ö': r'\"o',
    'ü': r'\"u', 'á': r"\'a", 'í': r"\'i",
}

def tex(s: str) -> str:
    out=[]
    for ch in s:
        if ch in ASCII_ESC:
            out.append(ASCII_ESC[ch])
        elif ch in UNICODE:
            out.append(UNICODE[ch])
        elif ord(ch) < 128:
            out.append(ch)
        else:
            # Preserve auditability while keeping pdflatex robust.
            out.append('?')
    return ''.join(out)

rows=list(csv.DictReader(CSV.open(encoding='utf-8')))
lines=[
 r'\begingroup\scriptsize',
 r'\setlength{\tabcolsep}{2pt}',
 r'\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.045\textwidth}>{\raggedright\arraybackslash}p{0.075\textwidth}>{\raggedright\arraybackslash}p{0.12\textwidth}>{\raggedright\arraybackslash}p{0.29\textwidth}>{\centering\arraybackslash}p{0.04\textwidth}>{\raggedright\arraybackslash}p{0.095\textwidth}>{\raggedright\arraybackslash}p{0.245\textwidth}@{}}',
 r'\toprule',
 r'ID & Source & Topic & Claim & St. & Report & Constructive reading\\',
 r'\midrule', r'\endfirsthead', r'\toprule',
 r'ID & Source & Topic & Claim & St. & Report & Constructive reading\\',
 r'\midrule', r'\endhead',
 r'\midrule\multicolumn{7}{r}{Continued on next page}\\', r'\endfoot',
 r'\bottomrule', r'\endlastfoot'
]
for r in rows:
    source = r['source'].replace('Wikipedia/MathWorld', 'WP/MW')
    source = source.replace('Wikipedia', 'WP').replace('MathWorld', 'MW')
    lines.append(r'{} & {} & {} & {} & \status{} & {} & {}\\'.format(
        tex(r['id']), tex(source), tex(r['topic']), tex(r['claim']),
        r['status'], tex(r['report_location']), tex(r['constructive_form'])))
lines += [r'\end{longtable}',r'\endgroup']
OUT.write_text('\n'.join(lines)+'\n',encoding='ascii')
print(f'wrote {OUT} with {len(rows)} rows')
