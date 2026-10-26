#!/usr/bin/env python3
"""Independently parse every printed coefficient and pivot pair."""
from pathlib import Path
from collections import Counter
import json,re
ROOT=Path(__file__).resolve().parents[1]

def need(x,msg):
    if not x:raise ValueError(msg)

def parse_formula(s):
    s=re.sub(r'\\(?:begin|end)\{align\*\}','',s)
    s=re.sub(r'Q_\{\d+\}=','',s)
    s=s.replace('\\\\','').replace('&','').replace('{}','')
    s=re.sub(r'\s+','',s)
    if s and s[0] not in '+-':s='+'+s
    terms=[]
    for sign,term in re.findall(r'([+-])([^+-]+)',s):
        match=re.match(r'\d+',term)
        c=int(match.group()) if match else 1
        if match:term=term[match.end():]
        mon=[]
        while term:
            m=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',term)
            need(m is not None,'unparsed TeX term '+term)
            mon.extend([int(m.group(1))]*int(m.group(2) or 1));term=term[m.end():]
        terms.append([c if sign=='+' else -c,mon])
    return terms

def main():
    source=json.loads((ROOT/'source/equation216.json').read_text())
    printed=(ROOT/'report/residuals.tex').read_text()
    blocks=re.findall(r'% BEGIN_RESIDUAL (\d+)\n(.*?)% END_RESIDUAL \1',printed,re.S)
    expected=[i for i in range(153) if i not in {97,98,99,100,101,102,149,150,151,152}]
    need([int(i) for i,s in blocks]==expected,'all 143 rows in order')
    count=0
    for index,formula in blocks:
        terms=parse_formula(formula)
        need(terms==source['residuals'][int(index)]['terms'],'printed coefficient mismatch '+index)
        count+=len(terms)
    cert=json.loads((ROOT/'equations/P207_certificate.json').read_text())
    portlines=[s for s in (ROOT/'report/ports.tex').read_text().splitlines() if re.match(r'^\d+ &',s)]
    need(len(portlines)==len(cert['ports']['requests'])==17,'seventeen printed ports')
    for line,port in zip(portlines,cert['ports']['requests']):
        fields=[s.strip().strip('$') for s in line.removesuffix(r'\\').split('&')]
        need(int(fields[0])==port['number'] and int(fields[1])==port['group'],'printed request and group')
        for key,formula in zip(['m','k','D','Y','Z'],fields[2:]):
            if formula=='h':
                need(port['number']==17 and key=='k','derived-index abbreviation')
            else:need(parse_formula(formula)==port[key],'printed port formula '+str(port['number'])+' '+key)
    results=json.loads((ROOT/'higher_degree/RESULTS.json').read_text())
    resultlines=[s for s in (ROOT/'report/results.tex').read_text().splitlines() if re.match(r'^\d+ &',s)]
    need(len(resultlines)==len(results)==9,'nine printed profiles')
    for line,r in zip(resultlines,results):
        fields=[s.strip() for s in line.removesuffix(r'\\').split('&')]
        values=[int(s.replace(',','')) for s in fields[:4]]
        need(values==[r[k] for k in ['variables','degree','residuals','live_binary_operations']],'printed profile values')
        need(fields[4]=='$2^{'+str(r['coefficient_height_bound_exponent'])+'}$','printed height bound')
    p=(ROOT/'report/pivots.tex').read_text()
    sections=re.split(r'\\subsection\*\{',p)[1:]
    need(len(sections)==len(results),'nine pivot sections')
    pivots=0
    for section,r in zip(sections,results):
        doc=json.loads((ROOT/'higher_degree/equations'/r['file']).read_text())
        pairs=[{'row':int(a),'variable':int(b)} for a,b in re.findall(r'\$\((\d+),(\d+)\)\$',section)]
        need(pairs==doc['elimination_steps'],'printed pivot mismatch '+r['file'])
        need(r['base_file'] in section,'printed seed')
        pivots+=len(pairs)
    main=(ROOT/'report/report.tex').read_text()
    flat=main
    for stem in ['results','ports','residuals','pivots']:
        flat=flat.replace('\\input{'+stem+'.tex}',(ROOT/'report'/f'{stem}.tex').read_text())
    need(flat==(ROOT/'report/report_standalone.tex').read_text(),'standalone source matches')
    print(json.dumps({'status':'PASS','printed_rows':143,'printed_terms':count,'printed_ports':17,'printed_profiles':9,'printed_pivots':pivots,'standalone_matches':True}))
if __name__=='__main__':main()
