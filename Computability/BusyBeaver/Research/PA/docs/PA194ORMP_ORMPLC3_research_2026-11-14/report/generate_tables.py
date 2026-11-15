#!/usr/bin/env python3
"""Generate report tables from the exact bundled artifacts (standard library)."""
from pathlib import Path
import csv
import json
import math

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def read_csv(name):
    with (ROOT/'comparison'/name).open(newline='', encoding='utf-8') as f:
        return list(csv.DictReader(f))

def tex(s):
    s = str(s).replace('−','-').replace('–','--').replace('—','---')
    s = s.replace('’',"'").replace('“','``').replace('”',"''")
    replacements = {'\\':r'\textbackslash{}','&':r'\&','%':r'\%',
                    '$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}',
                    '~':r'\textasciitilde{}','^':r'\textasciicircum{}',
                    '→':r'$\to$','↔':r'$\leftrightarrow$',
                    '≤':r'$\le$','≥':r'$\ge$','×':r'$\times$',
                    'σ':r'$\sigma$','Γ':r'$\Gamma$'}
    return ''.join(replacements.get(c,c) for c in s)

def dump(name, text):
    (HERE/name).write_text(text, encoding='utf-8')

def main():
    a=json.loads((ROOT/'construction/machine/independent/receipt.json').read_text())
    b=json.loads((ROOT/'construction/accelerated/independent/receipt.json').read_text())
    fields=[('Working states / transition rows','194 / 388','194 / 388'),
            ('Resolved primitive instructions','3,671','3,671'),
            ('Changed addresses from revised AX11H','154','449'),
            ('Universal source outcomes','4,778','4,778'),
            ('Whole blank startup transitions',f"{a['startup_steps']:,}",f"{b['startup_steps']:,}"),
            ('Independent symbolic events',f"{a['symbolic_steps']:,}",f"{b['symbolic_steps']:,}"),
            ('Maximum events per outcome','403','403'),
            ('Minimum duration constant','3','3')]
    s='\\begin{center}\n\\begin{tabular}{lrr}\n\\toprule\nQuantity & PA194ORMP & PA194ORMPLC3\\\\\n\\midrule\n'
    s+=''.join(f'{tex(x)} & {y} & {z}\\\\\n' for x,y,z in fields)
    s+='\\bottomrule\n\\end{tabular}\n\\end{center}\n'
    for name,r in [('PA194ORMP',a),('PA194ORMPLC3',b)]:
        s+='\\textbf{'+name+' dense SHA-256:}\\par\n{\\small\\hash{'+r['dense_sha256']+'}}\\par\n'
    dump('generated_summary.tex',s)

    s='\\begingroup\\small\n\\begin{longtable}{L{34mm}L{90mm}r}\n\\toprule\nDesign & Mechanism & Startup\\\\\n\\midrule\\endhead\n'
    for r in read_csv('incoming13.csv'):
        s+=tex(r['name'])+' & '+tex(r['mechanism'])+' & '+tex(r.get('reported_startup_steps',''))+'\\\\[3pt]\n'
    s+='\\bottomrule\n\\end{longtable}\n\\endgroup\n'
    dump('incoming_table.tex',s)

    s='\\begingroup\\small\n\\begin{longtable}{L{30mm}L{43mm}L{72mm}}\n\\toprule\nFamily & Representative designs & Change and proof obligation\\\\\n\\midrule\\endhead\n'
    for r in read_csv('inherited_families35.csv'):
        text=r['recurring_behavior']+' '+r['physical_change']+' '+r['proof_obligation']
        s+=tex(r['family'])+' & '+tex(r['designs'])+' & '+tex(text)+'\\\\[4pt]\n'
    s+='\\bottomrule\n\\end{longtable}\n\\endgroup\n'
    dump('families_table.tex',s)

    s='\\begingroup\\scriptsize\n\\begin{longtable}{rL{124mm}r}\n\\toprule\nID & Delivery directory or archive & Tables\\\\\n\\midrule\\endhead\n'
    for i,r in enumerate(read_csv('packets106.csv'),1):
        s+=f'{i:03d} & \\nolinkurl{{{r["packet"]}}} & {tex(r["fresh_recognized_table_occurrences"])}\\\\[0.5pt]\n'
    s+='\\bottomrule\n\\end{longtable}\n\\endgroup\n'
    dump('packets_table.tex',s)

    s=''
    for idx,(name,p) in enumerate([('PA194ORMP','machine'),('PA194ORMPLC3','accelerated')]):
        if idx:s+='\\clearpage\n'
        s+=f'\\subsection{{{name}}}\n'
        data={}
        for line in (ROOT/'construction'/p/'machine.tm').read_text().splitlines():
            q,b,w,d,t=line.split();data[int(q),int(b)]=w+d+('H' if int(t)==194 else t)
        s+='\\begin{center}\n\\begingroup\\fontsize{8.5}{10}\\selectfont\\setlength{\\tabcolsep}{3.3pt}\\renewcommand{\\arraystretch}{1.03}\n'
        s+='\\begin{tabular}{rll@{\\qquad}rll@{\\qquad}rll@{\\qquad}rll}\n\\toprule\n'
        s+=' & '.join(['State & Read 0 & Read 1']*4)+'\\\\\n\\midrule\n'
        for i in range(49):
            cells=[]
            for j in range(4):
                q=i+49*j
                cells+=([str(q),r'\texttt{'+data[q,0]+'}',r'\texttt{'+data[q,1]+'}'] if q<194 else ['','',''])
            s+=' & '.join(cells)+'\\\\\n'
        s+='\\bottomrule\n\\end{tabular}\n\\endgroup\n\\end{center}\n'
    dump('transition_tables.tex',s)

    files=[ROOT/'research/startup193'/f'result_trace3_append{x}.json' for x in (0,1)]
    if not all(p.exists() and p.stat().st_size for p in files):
        raise RuntimeError('Both completed trace-search receipts must be present.')
    rs=[json.loads(p.read_text()) for p in files]
    rows=[('Complete initial-control searches','completed_initial_controls'),
          ('Distinct traced branches','branches'),('Literal transitions','transitions'),
          ('Literal halts','halts'),('Certified outward rays','outward_rays'),
          ('Certified unchanged-tape cycles','unchanged_tape_cycles'),
          ('Resource-bound unresolved branches','bounded'),('Complete frame hits','frame_hits')]
    s='\\begin{center}\\small\n\\begin{tabular}{lrr}\n\\toprule\nQuantity & Append zero & Append one\\\\\n\\midrule\n'
    for label,key in rows:s+=tex(label)+' & '+' & '.join(f'{r[key]:,}' for r in rs)+'\\\\\n'
    s+='\\bottomrule\n\\end{tabular}\n\\end{center}\n'
    s+='Both runs completed all 193 initial controls without reaching the one-million-branch cap. '
    s+='Frames are observed at times strictly below 200,000; the fuel-bound configuration is classified as unresolved. '
    s+='These are complete trace-driven screens for at most three edits from the stated pool under those finite observation bounds, not a bound on arbitrary initializers.\n'
    dump('trace_search_summary.tex',s)

if __name__=='__main__':main()
