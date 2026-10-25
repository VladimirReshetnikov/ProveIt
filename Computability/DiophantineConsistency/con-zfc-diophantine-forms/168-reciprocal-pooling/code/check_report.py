#!/usr/bin/env python3
"""Independently parse every displayed residual back to an integer polynomial.

This checker imports no renderer or producer. It also checks the complete
companion formula against the literal final data and its degree witness.
"""
import hashlib
import json
from pathlib import Path
import re
from collections import Counter

ROOT=Path(__file__).resolve().parents[1]


def demand(ok,message):
    if not ok: raise ValueError(message)


def poly(terms):
    result=Counter()
    for c,m in terms: result[tuple(m)]+=c
    return {m:c for m,c in result.items() if c}


def plus(p,q,k=1):
    r=Counter(p)
    for m,c in q.items():r[m]+=k*c
    return {m:c for m,c in r.items() if c}


def times(p,q):
    r=Counter()
    for m,c in p.items():
        for n,d in q.items():r[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in r.items() if c}


def parse_math(expression):
    expression=re.sub(r'\s+','',expression).replace('&','').replace(r'\\','')
    terms=re.findall(r'[+-]?[^+-]+',expression)
    out=Counter()
    demand(''.join(terms)==expression,'unparsed TeX expression')
    for term in terms:
        sign=-1 if term.startswith('-') else 1
        term=term.lstrip('+-')
        match=re.match(r'\d+',term)
        c=int(match.group()) if match else 1
        tail=term[len(match.group()) if match else 0:]
        mon=[]
        while tail:
            m=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',tail)
            demand(m is not None,'invalid mathematical token: '+tail)
            mon.extend([int(m.group(1))]*int(m.group(2) or 1))
            tail=tail[m.end():]
        out[tuple(sorted(mon))]+=sign*c
    return {m:c for m,c in out.items() if c}


def main():
    qeq=json.loads((ROOT/'equations/quartic218/equation.json').read_text())
    deq=json.loads((ROOT/'equations/decic215/equation.json').read_text())
    source=(ROOT/'report/residuals218.tex').read_text()
    displays=re.findall(r'\\begin\{aligned\}(.*?)\\end\{aligned\}',source,re.S)
    demand(len(displays)==155,'wrong number of printed residuals')
    count=0
    for i,(display,row) in enumerate(zip(displays,qeq['residuals'])):
        match=re.match(r'\s*Q_\{(\d+)\}=\{\}&',display)
        demand(match is not None and int(match.group(1))==i,'incorrect printed residual label')
        actual=parse_math(display[match.end():])
        demand(actual==poly(row['terms']),f'printed residual {i} differs from coefficient data')
        count+=len(actual)
    # Check the report's explicit companion formula using exact polynomial arithmetic.
    hats=[{m:c for m,c in poly(r['terms']).items() if all(j<214 for j in m)} for r in qeq['residuals']]
    q={(95,):1,():-1}; qplus={(95,):1}; A={(135,):1,():1}
    one={():1};z={(214,):1}
    t0=plus(plus(times(A,q),times(A,q)),times(q,q),-1);t0=plus(t0,one,-1)
    t1=plus(plus(times(A,qplus),times(A,qplus)),times(qplus,qplus),-1);t1=plus(t1,one,-1)
    e0=plus(hats[154],times(q,hats[153]))
    e1=plus(hats[152],times(qplus,hats[151]))
    r=plus(plus(times(e0,t1),times(e1,t0)),times(z,times(t0,t1)),-1)
    demand([poly(row['terms']) for row in deq['residuals'][:151]]==hats[:151],'companion retained rows differ')
    demand(poly(deq['residuals'][151]['terms'])==r,'displayed companion formula differs')
    expansion=json.loads((ROOT/'equations/decic215/expanded_polynomial.json').read_text())
    demand(poly(expansion['terms']).get(tuple([95]*8+[214]*2))==1,'degree-ten witness differs')
    body=(ROOT/'report/report.tex').read_text()
    for snippet in [r'q=v_{95}-1',r'A=v_{135}+1',r'E_0&=\widehat Q_{154}+q\widehat Q_{153}',
                    r'E_1&=\widehat Q_{152}+(q+1)\widehat Q_{151}',r'\sum_{i=0}^{150}\widehat Q_i(v)^2+\mathcal R(v)^2=0']:
        demand(snippet in body,'report formula changed without checker update: '+snippet)
    ids=(ROOT/'report/identities.tex').read_text().replace(r'\newline ','')
    for path in ['equations/quartic218/equation.json','equations/quartic218/expanded_polynomial.json',
                 'equations/decic215/equation.json','equations/decic215/expanded_polynomial.json']:
        demand(hashlib.sha256((ROOT/path).read_bytes()).hexdigest() in ids,'printed artifact identity differs')
    # Reject an actual math corruption rather than trusting generated comments or hashes.
    sample=parse_math('x_{0}^{2}+2x_{1}-3')
    demand(sample=={(0,0):1,(1,):2,():-3},'parser control')
    demand(parse_math('x_{0}^{2}+3x_{1}-3')!=sample,'mutation control')
    print(json.dumps({'status':'PASS','printed_residuals':155,'parsed_residual_terms':count,
                      'companion_formula_exact':True,'degree_ten_witness':True,'identity_digests':4}))


if __name__=='__main__':main()
