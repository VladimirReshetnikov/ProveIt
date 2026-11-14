#!/usr/bin/env python3
"""Generate report tables from delivered machine/evidence and comparison data."""
from pathlib import Path
import csv,json,re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def esc(s):
    table={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$',
           '#':r'\#','_':r'\_\allowbreak{}','{':r'\{','}':r'\}',
           '~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
    return ''.join(table.get(c,c) for c in str(s))

def prose(s):
    bits=re.split(r'(`[^`]+`)',s)
    return ''.join(r'\nolinkurl{'+x[1:-1]+'}' if x.startswith('`') and x.endswith('`') else esc(x) for x in bits)

def table_header(spec,head):
    return (r'\begingroup'+'\n'+r'\small\raggedright\setlength{\tabcolsep}{3pt}'+'\n'
            +r'\begin{longtable}{'+spec+'}\n'+r'\toprule'+'\n'+head+r'\\\midrule\endfirsthead'+'\n'
            +r'\toprule'+'\n'+head+r'\\\midrule\endhead'+'\n')

def finish(s):return s+r'\bottomrule'+'\n'+r'\end{longtable}'+'\n'+r'\endgroup'+'\n'

def main():
    case=json.loads((ROOT/'machine/receipt.json').read_text())
    child=json.loads((ROOT/'machine/independent/receipt.json').read_text())
    parent=json.loads((ROOT/'baseline/independent/receipt.json').read_text())
    assert child['status']==parent['status']=='PASS'
    assert child['source_outcomes']==parent['source_outcomes']==4780
    (HERE/'verification_numbers.tex').write_text('% Automatically bound to completed receipts.\n'+
        '\\newcommand{\\IndependentSteps}{'+f"{child['symbolic_steps']:,}"+'}\n')
    rows=[('Working controls / rows','194 / 388','194 / 388'),
          ('Resolved source sites',f"{parent['source_sites']:,}",f"{child['source_sites']:,}"),
          ('Universal source outcomes',f"{parent['source_outcomes']:,}",f"{child['source_outcomes']:,}"),
          ('Independent symbolic operations',f"{parent['symbolic_steps']:,}",f"{child['symbolic_steps']:,}"),
          ('Maximum symbolic operations per case',str(parent['maximum_symbolic_steps']),str(child['maximum_symbolic_steps'])),
          ('Minimum positive-duration constant',str(parent['minimum_positive_duration_constant']),str(child['minimum_positive_duration_constant'])),
          ('List lemmas rederived from literal rows','4','4'),
          ('Whole blank initialization steps',f"{parent['startup_steps']:,}",f"{child['startup_steps']:,}")]
    s='\\begin{center}\n\\begin{tabular}{@{}lrr@{}}\n\\toprule\nCheck & Primary PA194 & PA1944L\\\\\\midrule\n'
    for row in rows:s+=' & '.join(row)+r'\\'+'\n'
    s+='\\bottomrule\n\\end{tabular}\n\\end{center}\n'
    (HERE/'verification_table.tex').write_text(s)
    parsed={}
    for ln in (ROOT/'machine/machine.tm').read_text().splitlines():
        q,b,w,d,n=ln.split();parsed[int(q),int(b)]=(int(w),d,int(n))
    assert len(parsed)==388
    def action(q,b):
        w,d,n=parsed[q,b]
        return f'${w}{d}\\,{"H" if n==194 else n}$'
    s='\\begin{center}\n\\footnotesize\\setlength{\\tabcolsep}{5pt}\n\\begin{tabular}{rrr@{\\hspace{8pt}}rrr@{\\hspace{8pt}}rrr@{\\hspace{8pt}}rrr}\n\\toprule\n'
    s+=' & '.join(['$q$ & Read 0 & Read 1']*4)+r'\\\midrule'+'\n'
    for i in range(49):
        parts=[]
        for block in range(4):
            q=i+49*block
            parts.extend([str(q),action(q,0),action(q,1)] if q<194 else ['','',''])
        s+=' & '.join(parts)+r'\\'+'\n'
    s+='\\bottomrule\n\\end{tabular}\n\\end{center}\n'
    (HERE/'transition_table.tex').write_text(s)
    packets=list(csv.DictReader((ROOT/'comparison/packet_ledger.csv').open()))
    assert len(packets)==72
    s=table_header('@{}p{0.035\\linewidth}p{0.325\\linewidth}p{0.60\\linewidth}@{}','No. & Packet & Reported contribution')
    for i,p in enumerate(packets,1):
        s+=f"{i} & \\nolinkurl{{{p['packet']}}} & {prose(p['reported_contribution'])}"+r'\\[5pt]'+'\n'
    (HERE/'packet_ledger_reflow.tex').write_text(finish(s))
    frontier=list(csv.DictReader((ROOT/'comparison/frontier194.csv').open()))
    assert len(frontier)==82
    categories={'reported principal construction':'Principal','supplementary construction':'Supplement',
       'source-validated research rotation':'Source rotation','research auxiliary':'Research','rejected':'Rejected'}
    s=table_header('@{}p{0.035\\linewidth}p{0.235\\linewidth}p{0.135\\linewidth}p{0.55\\linewidth}@{}','No. & Name & Category & Mechanism and evidence')
    s=s.replace(r'\small\raggedright',r'\fontsize{9}{10.2}\selectfont\raggedright',1)
    for i,p in enumerate(frontier,1):
        s+=f"{i} & {esc(p['name'])} & {categories[p['evidence_category']]} & {prose(p['mechanism'])}"+r'\\[4pt]'+'\n'
    (HERE/'frontier194_reflow.tex').write_text(finish(s))
    theory=(ROOT/'theory/bounded_compiler_and_radix3.tex').read_text()
    stop=theory.find(r'\begin{thebibliography}')
    if stop<0:stop=theory.rindex(r'\end{document}')
    body=theory[theory.index(r'\section{'):stop]
    (HERE/'theory_sections.tex').write_text('% Exact mathematical sections from theory supplement.\n'+body)
    print('Generated report inputs from completed receipts and complete ledgers.')

if __name__=='__main__':main()
