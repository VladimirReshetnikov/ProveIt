#!/usr/bin/env python3
"""Generate report macros and the complete transition table from checked data."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT))
import build

table_path=ROOT/'machines/k226.tm'; raw=table_path.read_bytes()
table=build.parse(raw,0,226)
record=json.loads((ROOT/'evidence/runtime226.json').read_text())
assert record['status']=='UNIVERSAL_MATHEMATICAL_PASS' and record['cases']==6656
assert record['table_sha256']==hashlib.sha256((ROOT/'machines/k226_old.tm').read_bytes()).hexdigest()
macros={'CandidateStates':'226','TransitionRows':'452','RuleCount':format(record['symbolic_steps'],','),
        'MaximumSymbolic':str(record['maximum_symbolic_steps']),'SourceDepth':str(record['metrics']['maximum_depth']),
        'CanonicalHash':hashlib.sha256(raw).hexdigest(),'InheritedHash':record['table_sha256']}
(HERE/'results.tex').write_text(''.join('\\newcommand{\\'+k+'}{'+v+'}\n' for k,v in macros.items()))
def entry(q,b):
    w,d,z=table[q,b]
    return str(w)+('R' if d==1 else 'L')+('H' if z==226 else str(z))
lines=[r'\begingroup\small\ttfamily',
       r'\setlength{\tabcolsep}{5pt}',
       r'\begin{longtable}{@{}rll@{\hspace{7mm}}rll@{\hspace{7mm}}rll@{}}',
       r'\toprule',r'\textrm{State}&\textrm{Read 0}&\textrm{Read 1}&\textrm{State}&\textrm{Read 0}&\textrm{Read 1}&\textrm{State}&\textrm{Read 0}&\textrm{Read 1}\\',
       r'\midrule\endfirsthead',r'\toprule',
       r'\textrm{State}&\textrm{Read 0}&\textrm{Read 1}&\textrm{State}&\textrm{Read 0}&\textrm{Read 1}&\textrm{State}&\textrm{Read 0}&\textrm{Read 1}\\',
       r'\midrule\endhead',r'\midrule\multicolumn{9}{r}{\textrm{Continued on next page}}\\\endfoot',r'\bottomrule\endlastfoot']
for i in range(76):
    fields=[]
    for q in (i,i+76,i+152):
        fields.extend([str(q),entry(q,0),entry(q,1)] if q<226 else ['','',''])
    lines.append(' & '.join(fields)+r'\\')
lines.extend([r'\end{longtable}',r'\endgroup'])
(HERE/'transition_table.tex').write_text('\n'.join(lines)+'\n')
print(json.dumps(macros,indent=2))
