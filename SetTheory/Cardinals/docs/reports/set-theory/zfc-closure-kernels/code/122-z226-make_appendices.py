#!/usr/bin/env python3
"""Generate report facts and its complete table from the frozen machine files."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def main():
    path = ROOT/'machines/k226.tm'
    rows = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,z = line.split()
            rows[int(q),int(b)] = w+d+z
    assert set(rows) == {(q,b) for q in range(226) for b in (0,1)}
    runtime = json.loads((ROOT/'evidence/runtime226.json').read_text())
    assert runtime['status'] == 'UNIVERSAL_MATHEMATICAL_PASS'
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    facts = dict(CandidateStates=226, CandidateLastState=225, CandidateRows=len(rows),
                 SourceLeaves=5121, RuntimeCases=runtime['cases'], BootTicks=409835,
                 RuntimeRules=runtime['symbolic_steps'], MinimumTicks=runtime['minimum_actual_steps'],
                 CandidateHashA=digest[:32], CandidateHashB=digest[32:])
    (ROOT/'sections/facts.tex').write_text(''.join(
        '\\newcommand{\\'+key+'}{'+str(value)+'}\n' for key,value in facts.items()))
    header = ('State & Read 0 & Read 1 & State & Read 0 & Read 1 & '
              'State & Read 0 & Read 1 \\\\\n')
    text = ('{\\small\\setlength{\\tabcolsep}{4pt}\n'
            '\\begin{longtable}{@{}rll@{\\hspace{8mm}}rll@{\\hspace{8mm}}rll@{}}\n'
            '\\toprule\n'+header+'\\midrule\\endfirsthead\n'
            '\\toprule\n'+header+'\\midrule\\endhead\n'
            '\\bottomrule\\endfoot\n')
    for line in range(76):
        cells = []
        for q in (line,line+76,line+152):
            cells += ([str(q),'\\texttt{'+rows[q,0]+'}','\\texttt{'+rows[q,1]+'}']
                      if q < 226 else ['','',''])
        text += ' & '.join(cells)+' \\\\\n'
    text += '\\end{longtable}\n}\n'
    (ROOT/'sections/machine_table.tex').write_text(text)
    print('Generated facts and all 452 literal table entries.')


if __name__ == '__main__':
    main()
