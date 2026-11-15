#!/usr/bin/env python3
"""Generate report tables from the frozen, independently checked artifacts."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
NAMES = ('PA194AX11GH', 'PA194AX11GHS')


def esc(text):
    text = str(text).replace('\u2013', '--').replace('\u2014', '---')
    chars = {'&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#', '_': r'\_',
             '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}',
             '^': r'\textasciicircum{}', '\\': r'\textbackslash{}'}
    return ''.join(chars.get(c, c) for c in text)


def load(p):
    return json.loads(p.read_text())


def main():
    literals = [load(ROOT/'verification/independent/recorded'/n/'receipt.json') for n in NAMES]
    sources = [load(ROOT/'verification/source'/n/'receipt.json') for n in NAMES]
    rows = [
        ('Working controls / transitions', '194 / 388', '194 / 388'),
        ('Fixed controls + readers - folds', r'$134+67-7$', r'$135+67-8$'),
        ('Primitive source sites', '3,671', '3,668'),
        ('Universal source outcomes', '4,778', '4,774'),
        ('Complete blank startup', '57,922', '57,768'),
        ('Local simultaneous-fold cases', '28', '32'),
        ('Independent arithmetic template instances', '947', '945'),
        ('Independent literal symbolic operations', *(f"{r['symbolic_steps']:,}" for r in literals)),
        ('Maximum symbolic operations per outcome', *(str(r['maximum_symbolic_steps']) for r in literals)),
        ('Minimum exact-duration constant', *(str(r['minimum_positive_duration_constant']) for r in literals)),
    ]
    text = ['\\begin{center}\\small', r'\begin{tabular}{@{}lrr@{}}\toprule',
            r'Property&AX11GH&AX11GHS\\\midrule']
    text += [' & '.join(r)+r'\\' for r in rows]
    text += [r'\bottomrule\end{tabular}\end{center}']
    for n, r in zip(NAMES, literals):
        text += [r'\textbf{'+n+r' SHA-256:}\\',
                 r'{\small\ttfamily\nolinkurl{'+r['dense_sha256']+r'}}\par']
    (HERE/'results_table.tex').write_text('\n'.join(text)+'\n')

    tables=[]
    for n in NAMES:
        table={}
        for line in (ROOT/'machines'/n/'machine.tm').read_text().splitlines():
            q,b,w,d,t=line.split(); table[int(q),int(b)]=w+d+t
        assert len(table)==388
        tables.append(table)
    text=[r'{\small\setlength{\tabcolsep}{12pt}',
          r'\begin{longtable}{rllll}\toprule',
          r'&\multicolumn{2}{c}{AX11GH}&\multicolumn{2}{c}{AX11GHS}\\',
          r'State&Read 0&Read 1&Read 0&Read 1\\\midrule\endhead']
    for q in range(194):
        actions=[str(q)]+[r'\texttt{'+t[q,b]+'}' for t in tables for b in (0,1)]
        text.append(' & '.join(actions)+r'\\')
    text += [r'\bottomrule\end{longtable}}']
    (HERE/'transition_tables.tex').write_text('\n'.join(text)+'\n')

    designs=load(ROOT/'comparison/designs194.json')
    assert len(designs)==110
    categories={'reported principal construction':'Principal', 'supplementary construction':'Supplement',
                'research auxiliary':'Auxiliary','research seed':'Seed',
                'rejected':'Rejected','rejected diagnostic':'Rejected diagnostic'}
    rank={'Principal':0,'Supplement':1,'Seed':2,'Auxiliary':3,'Rejected':4,'Rejected diagnostic':5}
    designs.sort(key=lambda d:(rank[categories[d['category']]],d['name'],d['canonical_class']))
    text=[r'{\footnotesize\setlength{\tabcolsep}{4pt}',
          r'\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.14\textwidth}>{\raggedright\arraybackslash}p{0.23\textwidth}>{\raggedright\arraybackslash}p{0.12\textwidth}>{\raggedright\arraybackslash}p{0.46\textwidth}@{}}',
          r'\toprule Graph hash&Name&Role&Mechanism attributed to source\\\midrule\endhead']
    for d in designs:
        text.append(' & '.join([r'\texttt{'+d['canonical_class'][:12]+'}',esc(d['name']),
                    esc(categories[d['category']]),esc(d['mechanism'])])+r'\\[3pt]')
    text += [r'\bottomrule\end{longtable}}']
    (HERE/'class_table.tex').write_text('\n'.join(text)+'\n')

    grammar=load(ROOT/'research/grammar/summary.json')
    experiments=[
        ('Register aliases','263,888 abstract states; all 36 pairs','No direct alias'),
        ('301/88 plus helper row','5,649,890 specifications','18 local survivors; no clean seed'),
        ('16/122 plus helper row','4,791,766 specifications','No local survivor'),
        ('New GH control merge','30,818 windows; radius 6; join limit 180 steps','No candidate'),
        ('New GH control elimination','Same conservative windows and join bound','No candidate'),
        ('ZFC marker relay','Literal new-GH transplantation','Source failure; ray after 117 steps'),
    ]
    for name,g in zip(('GH grammar search','GHS grammar search'),grammar):
        experiments.append((name,f"{g['iterations']:,} proposals; 420 seconds",'Best reader score 60; no score 59'))
    text=[r'\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.25\textwidth}>{\raggedright\arraybackslash}p{0.35\textwidth}>{\raggedright\arraybackslash}p{0.33\textwidth}@{}}\toprule',
          r'Experiment&Completed scope&Result\\\midrule\endhead']
    text += [' & '.join(map(esc,r))+r'\\[4pt]' for r in experiments]
    text += [r'\bottomrule\end{longtable}']
    (HERE/'search_table.tex').write_text('\n'.join(text)+'\n')
    print('Generated both full tables, 110-class comparison, results and search tables.')


if __name__=='__main__':
    main()
