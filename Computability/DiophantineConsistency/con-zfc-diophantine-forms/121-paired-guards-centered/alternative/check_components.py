#!/usr/bin/env python3
"""Independent elementary regressions and literal SOS expansion (no builder imports)."""
from pathlib import Path
from collections import defaultdict
from math import comb,factorial,isqrt
import json,hashlib,argparse
HERE=Path(__file__).resolve().parent

def need(x,msg):
    if not x:raise ValueError(msg)
def check():
    represented=set()
    for a in range(51):
        for b in range(51):
            for c in range(51):represented.add(a*a+b*b+c*(c+1))
    need(set(range(2501))<=represented,'three-square positive regression')
    pair_cases=0
    for r in range(-50,51):
        for s in range(-50,51):
            if r+s>=0:
                need((r>=0 and s>=0)==(r*s>=0),'paired sign equivalence');pair_cases+=1
    need((-1)*(-1)==1 and -1+-1<0,'missing sum negative control')
    factorial_cases=0
    for t in range(1,9):
        target=factorial(t)
        for F in sorted(set(range(1,121))|{target,max(1,target-1),target+1}):
            for rho in (F*t*t,F*F*t*t,F*F*t*t+17):
                V=(rho+1)**t;D=comb(rho+t,t)
                ceiling=(V+D-1)//D
                need((ceiling==F)==(F==target),'wider factorial equivalence')
                if F==target:
                    s=D*F-V;r=D-s-1
                    need(r>=0 and s>=0 and D==r+s+1 and D*F==V+s,'factorial witnesses')
                factorial_cases+=1
    outputs=[]
    for variant,expected_n in [('paired',493),('squared_paired',489)]:
        eq=json.loads((HERE/variant/'equation.json').read_text());exp=json.loads((HERE/variant/'expanded_polynomial.json').read_text())
        need(eq['domain']=='unrestricted integers','domain')
        need(len(eq['variables'])==expected_n,'variable count')
        coefficients=defaultdict(int)
        for row in eq['residuals']:
            p=defaultdict(int)
            for c,m in row['terms']:
                need(all(type(i)is int and 0<=i<expected_n for i in m),'index bounds')
                need(type(c)is int and len(m)<=2,'integer quadratic row')
                p[tuple(sorted(m))]+=c
            for m,c in p.items():
                for n,d in p.items():coefficients[tuple(sorted(m+n))]+=c*d
        got={m:c for m,c in coefficients.items() if c}
        want={tuple(m):c for c,m in exp['terms']}
        need(got==want,'full sparse expansion identity')
        need(max(map(len,got))==4,'exact degree')
        outputs.append({'variant':variant,'variables':expected_n,'residuals':len(eq['residuals']),'monomials':len(got),'height':max(map(abs,got.values())),'equation_sha256':hashlib.sha256((HERE/variant/'equation.json').read_bytes()).hexdigest(),'expanded_sha256':hashlib.sha256((HERE/variant/'expanded_polynomial.json').read_bytes()).hexdigest()})
    return {'status':'PASS','pair_cases':pair_cases,'represented_naturals':2501,'factorial_cases':factorial_cases,'outputs':outputs,'scope':'Finite component checks and complete coefficient identities, not proof of consistency or a proof-assistant certificate.'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args();result=check();text=json.dumps(result,indent=2)+'\n';print(text,end='');
    if a.output:a.output.write_text(text)
