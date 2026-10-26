#!/usr/bin/env python3
"""Generate the literal mathematical appendices, then check their contents."""
import collections
import json
import re
from pathlib import Path

ROOT=Path(__file__).resolve().parent
REPORT=ROOT/'report'
PROFILES=['integer143_degree8','integer119_degree16','integer112_degree24','integer107_degree32','integer102_degree64']

def term(c,m):
    counts=collections.Counter(m)
    body=''.join('x_{'+str(i)+'}'+('^{'+str(e)+'}' if e>1 else '') for i,e in sorted(counts.items()))
    a=abs(c)
    return ('-' if c<0 else '+')+((str(a) if a!=1 or not m else '')+body)

def expression(terms):
    parts=[term(c,m) for c,m in terms]
    return ''.join(parts).lstrip('+') or '0'

def tex_polynomial_parse(s):
    s=re.sub(r'\s+','',s).replace('&','').replace(r'\\','')
    if not s.startswith(('+','-')):s='+'+s
    answer={}
    for tok in re.findall(r'[+-][^+-]+',s):
        sign=1 if tok[0]=='+' else -1;body=tok[1:]
        prefix=re.match(r'\d+',body);coef=int(prefix.group()) if prefix else 1
        if prefix:body=body[len(prefix.group()):]
        mon=[]
        while body:
            m=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',body)
            if not m:raise ValueError('Unparsed printed polynomial: '+body)
            mon += [int(m[1])]*int(m[2] or '1');body=body[len(m[0]):]
        key=tuple(sorted(mon));answer[key]=answer.get(key,0)+sign*coef
    return {k:v for k,v in answer.items() if v}

def main():
    REPORT.mkdir(exist_ok=True)
    src=json.loads((ROOT/'inputs/source216.json').read_text())
    interface=json.loads((ROOT/'inputs/interface216.json').read_text())
    rows=[]
    for i,r in enumerate(src['residuals']):
        parts=[term(c,m) for c,m in r['terms']];lines=[];line=''
        for p in parts:
            if line and len(line)+len(p)>130:lines.append(line);line=''
            line+=p
        if line:lines.append(line)
        lines[0]=lines[0].lstrip('+')
        printed=''.join(lines)
        if tex_polynomial_parse(printed)!={tuple(m):c for c,m in r['terms']}:raise ValueError('Printed residual mismatch')
        block=f'% BEGIN_RESIDUAL {i}\n'+r'\begin{align*}'+'\n'
        block+=f'r_{{{i}}}={{}}&'+lines[0]
        for line in lines[1:]:block+=r'\\'+'\n&'+line
        block+='\n'+r'\end{align*}'+f'\n% END_RESIDUAL {i}\n'
        rows.append(block)
    (REPORT/'residuals.tex').write_text(r'\begingroup\small\allowdisplaybreaks[4]'+'\n'+'\n'.join(rows)+'\n'+r'\endgroup'+'\n')
    table=[r'\begin{center}\small',r'\begin{tabular}{rrrrlll}',r'\toprule',r'Request & Block & $n$ & $m$ & $k$ & $D=X-AY$ & $(Y,Z)$\\',r'\midrule']
    membership={i:j for j,b in enumerate(interface['blocks']) for i in b['requests']}
    requestmeta=[]
    for q in interface['requests']:
        expressions={k:expression(q[k]) for k in ('n','m','k','D','Y','Z')}
        for k,p in expressions.items():
            if tex_polynomial_parse(p)!={tuple(m):c for c,m in q[k]}:raise ValueError('Printed request mismatch')
        if q['request']==17:expressions['k']='J'
        vals=[str(q['request']),str(membership[q['request']])]+['$'+expressions[k]+'$' for k in ('n','m','k','D')]+['$('+expressions['Y']+','+expressions['Z']+')$']
        table.append(' & '.join(vals)+r'\\')
        requestmeta.append({'request':q['request'],'block':membership[q['request']],**expressions})
    table += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (REPORT/'requests.tex').write_text('\n'.join(table)+'\n')
    pivot_text=[];all_metrics=[]
    for name in PROFILES:
        d=ROOT/'equations'/name;cert=json.loads((d/'projection.json').read_text());met=json.loads((d/'METRICS.json').read_text());all_metrics.append(met)
        n=met['variables'];degree=met['exact_total_degree']
        if n==102:pivot_text.append(r'\clearpage')
        pivot_text.append(r'\subsection{'+f'{n} integers, degree {degree}'+r'}')
        partition=r';\ '.join(','.join(map(str,part)) for part in cert['partition'])
        pivot_text.append(r'Block partition: $('+partition+r')$.')
        pivot_text.append(f"There are {len(cert['steps'])} deleted monic coordinates and {met['residuals']} final residuals.")
        pivot_text.append(r'\begin{center}\small\begin{tabular}{rrrrrr}\toprule')
        piv=[f"$({s['row']},{s['variable']})$" for s in cert['steps']]
        for i in range(0,len(piv),6):pivot_text.append(' & '.join(piv[i:i+6]+['']*(6-len(piv[i:i+6])))+r'\\')
        pivot_text.append(r'\bottomrule\end{tabular}\end{center}')
    (REPORT/'pivots.tex').write_text('\n'.join(pivot_text)+'\n')
    result=[r'Our principal recommendation is the fixed polynomial in \textbf{112 unrestricted integers of exact degree 24}. A lower-degree companion uses \textbf{119 integers at degree 16}; the smallest variable count in this release is \textbf{102 integers at degree 64}. Each has the required ZFC equivalence, with the dependency boundary described below.',r'\begin{center}',r'\begin{tabular}{rrrrr}',r'\toprule',r'Integer variables & Exact degree & Residuals & Height bound & Binary operations\\',r'\midrule']
    for m in all_metrics:
        result.append(f"{m['variables']} & {m['exact_total_degree']} & {m['residuals']} & $<2^{{{m['coefficient_height_strictly_less_than_2_power']}}}$ & {m['binary_operations']}"+r'\\')
    result += [r'\bottomrule',r'\end{tabular}',r'\end{center}',
      r'The 143-variable octic is a useful companion obtained with five singleton blocks and ordinary elimination; it does not need the new cross-base fusion theorem. The other four rows use that theorem. Operation counts describe the delivered literal evaluators and are not claimed optimal.',
      r'For comparison, package 152 gives 153 integers at degree 8, 125 at degree 16, 117 at degree 32, and 111 at degree 64 \cite{eliminate152}. The corresponding supplied coefficient-height bounds are $2^{47},2^{80},2^{144},2^{173}$. Our results lower the variable counts at those degrees; our degree-64 height bound $2^{214}$ is larger than the older bound $2^{173}$. Thus even this direct-family comparison has a coefficient tradeoff.',
      r'A fair local control isolates the new arithmetic gain. Apply exactly the principal form\textquotesingle s 95 core eliminations to the original source and also eliminate its three modulus coordinates and two already monic $K$ coordinates. This gives 116 integers, 53 residuals, and exact degree 24 without cross-base fusion. The new construction has 112 integers, 49 residuals, and the same degree. The four-coordinate saving in this matched comparison is attributable to the new fusion; the larger comparison against older packages also benefits from the improved source and generic elimination.']
    (REPORT/'results.tex').write_text('\n\n'.join(result)+'\n')
    master=(REPORT/'report.tex').read_text()
    flat=re.sub(r'\\input\{([^}]+)\}',lambda m:(REPORT/m[1]).read_text(),master)
    (REPORT/'ConZFC_Mixed_Base_Pooling.tex').write_text(flat)
    record={'status':'PASS','printed_source_residuals':len(src['residuals']),
            'printed_residual_terms':sum(len(r['terms']) for r in src['residuals']),
            'printed_power_requests':len(interface['requests']),
            'printed_monic_profiles':len(PROFILES),'monic_pivots':sum(m['deleted_monic_coordinates'] for m in all_metrics),
            'polynomial_text_parsed_back_exactly':True,'profiles':PROFILES,'request_table':requestmeta}
    (ROOT/'verification/PRINTED_EQUATIONS.json').write_text(json.dumps(record,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k!='request_table'},sort_keys=True))

if __name__=='__main__':main()
