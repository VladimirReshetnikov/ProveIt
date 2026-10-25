#!/usr/bin/env python3
"""Generate the report's literal data, never its mathematical conclusions."""
from pathlib import Path
from collections import Counter
import hashlib
import json

ROOT = Path(__file__).resolve().parent

def load(path):
    return json.loads((ROOT / path).read_text())

def esc(s):
    return s.replace('_', r'\_').replace('&', r'\&').replace('%', r'\%')

def number(n):
    return f'{n:,}'.replace(',', r'{,}')

def term(c, indices, first=False):
    sign = '-' if c < 0 else ('' if first else '+')
    counts = Counter(indices)
    coefficient = str(abs(c)) if abs(c) != 1 or not indices else ''
    monomial = ''.join('z_{' + str(i) + '}' +
                       ('^{' + str(k) + '}' if k > 1 else '')
                       for i, k in sorted(counts.items()))
    return sign + coefficient + monomial

def main():
    direct = load('direct/integer306/equation.json')
    dm = load('direct/integer306/METRICS.json')
    profiles = ['matched1252', 'principal985', 'sparse1122']
    gm = {p: load('graph/' + p + '/polynomial.json')['metrics'] for p in profiles}
    values = {'DirectVars': dm['variables'], 'DirectLast': dm['variables']-1,
              'DirectRows': dm['residuals'], 'DirectRowLast': dm['residuals']-1,
              'DirectTerms': dm['monomials'], 'DirectHeight': dm['coefficient_height']}
    (ROOT / 'metrics.tex').write_text('\n'.join(
        '\\newcommand{\\' + k + '}{' + number(v) + '}' for k, v in values.items())+'\n')
    rows = [
        ('Parent direct quartic [131]', 324, 4, 5808, 128446),
        ('New direct quartic', dm['variables'], dm['degree'], dm['monomials'], dm['coefficient_height']),
        ('Parent unit-coefficient quartic [127]', 2215, 4, 30468, 1),
        ('New graph, same 442-coordinate source', gm['matched1252']['variables'], 4, gm['matched1252']['monomials'], 1),
        ('New graph, fewer variables', gm['principal985']['variables'], 4, gm['principal985']['monomials'], 1),
        ('New graph, smaller support', gm['sparse1122']['variables'], 4, gm['sparse1122']['monomials'], 1),
    ]
    table = [r'\begin{table}[ht]', r'\centering\small',
             r'\begin{tabular}{@{}p{0.44\textwidth}rrrr@{}}\toprule',
             r'Construction & Variables & Degree & Terms & Height\\\midrule']
    table += [' & '.join([esc(name)]+[number(v) for v in vals])+r'\\' for name,*vals in rows]
    table += [r'\bottomrule\end{tabular}',
              r'\caption{All variables are unrestricted integers. Terms are fully collected nonzero monomials. The graph companions permit individual fourth powers.}',
              r'\label{tab:metrics}\end{table}']
    (ROOT / 'results_table.tex').write_text('\n'.join(table)+'\n')
    out = [r'\par\begingroup\small',
           r'\setlength{\abovedisplayskip}{4pt}\setlength{\belowdisplayskip}{5pt}']
    for j, row in enumerate(direct['residuals']):
        pieces = [term(c,m,i==0) for i,(c,m) in enumerate(row['terms'])]
        chunks=[]; current=''
        for piece in pieces:
            if current and len(current)+len(piece)>118:
                chunks.append(current); current=piece
            else: current+=piece
        if current: chunks.append(current)
        out.append(r'\par\noindent\begin{minipage}{\linewidth}')
        out.append(r'\noindent{\scriptsize\textsf{'+str(j)+': '+esc(row['label'])+'}}')
        out.append(r'\begin{align*}')
        out.append('r_{'+str(j)+r'}={}&'+chunks[0]+(r'\\[-2pt]' if len(chunks)>1 else ''))
        for k,line in enumerate(chunks[1:]):
            out.append('&'+line+(r'\\[-2pt]' if k<len(chunks)-2 else ''))
        out.append(r'\end{align*}')
        out.append(r'\end{minipage}\par')
    out.append(r'\endgroup')
    (ROOT / 'direct_residuals.tex').write_text('\n'.join(out)+'\n')
    identities = []
    for rel in ['direct/parent/integer324-equation.json',
                'direct/integer306/equation.json',
                'direct/integer306/expanded_polynomial.json'] + ['graph/'+p+'/polynomial.json' for p in profiles]:
        b=(ROOT/rel).read_bytes()
        identities.append({'path':rel,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
    (ROOT/'EQUATION_IDENTITIES.json').write_text(json.dumps(identities,sort_keys=True,indent=2)+'\n')
    provenance = [r'The comparison and retrieval pin is \srcpin. The direct parent comes from',
        r'\path{131-shared-pell-caps-round16/direct/integer324/}; the matched graph parent comes from',
        r'\path{127-graph-certificates/graph/principal/}. The 306-coordinate source is newly constructed here.',
        r'The complete per-file inventory is \path{MANIFEST.sha256}; this appendix records the normative equation identities.',
        r'\begingroup\small']
    for entry in identities:
        provenance += [r'\par\noindent\path{'+entry['path']+'}\\',
                       r'\mbox{'+f"{entry['bytes']:,}"+r' bytes.} SHA-256: \path{'+entry['sha256']+r'}.\par\smallskip']
    provenance += [r'\endgroup',
        r'The retained Lean interface files identify the inherited logical calibration. They are reference sources, not a complete standalone Lean project; their full transitive imports were not rebuilt for this release.']
    (ROOT/'provenance_section.tex').write_text('\n'.join(provenance)+'\n')
    print(json.dumps({'status':'generated','direct_residuals':len(direct['residuals']),
        'graphs':gm,'equation_identities':len(identities)},sort_keys=True))

if __name__ == '__main__':
    main()
