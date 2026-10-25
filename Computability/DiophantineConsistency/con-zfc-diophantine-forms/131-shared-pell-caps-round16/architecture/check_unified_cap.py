#!/usr/bin/env python3
"""Independent row/expansion audit, importing no producer code."""
from collections import defaultdict
from pathlib import Path
from math import comb,factorial,gcd,prod
import argparse,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
INC=HERE.parent/'intake/ConZFC_Shared_Pell_Bound_261_2026-10-24/ConZFC_Shared_Pell_Bound_261_2026-10-24'
spec=importlib.util.spec_from_file_location('independent_cap',HERE/'check_cap_variants.py')
ic=importlib.util.module_from_spec(spec);spec.loader.exec_module(ic)
need,add,mul,scale,const=ic.need,ic.add,ic.mul,ic.scale,ic.const

def norm(row):
    if isinstance(row,dict):row=row['terms']
    out=defaultdict(int)
    for c,m in row:out[tuple(sorted(m))]+=c
    return {m:c for m,c in out.items() if c}

def semantic(root):
    d=json.loads((root/'raw/raw_audit_input.json').read_text())
    f=d['factorials'][0];a=d['amplification'];r=d['radix']
    need(len(d['factorials'])==len(d['binomials'])==1,'factorial/binomial count')
    need(f['binomial']==d['product']['product']==d['binomials'][0]['output'],'fusion output')
    need(f['radius']==d['product']['square'],'fusion square')
    need(a['K']==a['R'],'K must equal R')
    reps=[n for n,k,mod,label in d['ranges'] if label!='crt.range.derived_label_sum']
    need(len(reps)==9 and len(d['ranges'])==10,'range counts')
    need(not any(z['label']=='crt.aggregate_representative_bound' for z in d['rows']),'obsolete cap')
    ports=[f[k] for k in ('input','output','binomial','numerator','remainder','slack')]
    ports += [a[k] for k in ('K','N')]+[r['H'],r['radix']]+reps
    ex=ic.Expander(d,{x[1] for x in ports if x[0]=='v'})
    atom=lambda z:const(z[1]) if z[0]=='c' else ex.variable(z[1])
    forced=lambda z:const(z[1]) if z[0]=='c' else ex.variable(z[1],force=True)
    F,B,V,u,v,t=[atom(f[k]) for k in ('output','binomial','numerator','remainder','slack','input')]
    matches=lambda label:[z for z in d['rows'] if z['label']==label]
    def row(label):
        z=matches(label);need(len(z)==1,'unique '+label);return ex.row(z[0])
    need(atom(f['radius'])==mul(F,F),'radius F²')
    need(atom(d['binomials'][0]['n'])==add(mul(F,F),t),'binomial F²+t')
    need(d['binomials'][0]['k']==f['input'],'binomial k')
    need(row('fact0.ceiling')==add(V,B,scale(-1,mul(B,F)),scale(-1,u),const(-1)),'ceiling')
    need(row('fact0.remainder_bound')==add(B,scale(-1,u),scale(-1,v),const(-1)),'ceiling interval')
    pc=[p for p in d['powers'] if p['output']==f['numerator']]
    need(len(pc)==1 and pc[0]['exponent']==f['input'] and atom(pc[0]['base'])==add(mul(F,F),const(1)),'V power')
    need(forced(r['H'])==add(const(1),*[atom(z) for z in reps]),'H representative sum')
    np=[p for p in d['powers'] if p['output']==a['N']]
    need(len(np)==1 and np[0]['base']==a['B'] and np[0]['exponent']==a['K'],'N=B^K')
    if r['kind'] in ('NH','BH'):
        qp=[p for p in d['powers'] if p['output']==r['radix']]
        need(len(qp)==1 and qp[0]['exponent']==a['K'],'q exponent')
        left=a['N'] if r['kind']=='NH' else a['B']
        need(atom(qp[0]['base'])==mul(atom(left),atom(r['H'])),'q base')
    else:
        need(r['kind']=='N_H','unknown radix')
        qp=[p for p in d['powers'] if p['base']==r['H'] and p['exponent']==a['K']]
        need(len(qp)==1,'H power')
        need(forced(r['radix'])==mul(atom(a['N']),atom(qp[0]['output'])),'q product')
    need(len(d['powers'])==18 and len(d['seeds'])==15,'power census')
    return ic.check(root/'raw/raw_audit_input.json')

def expansion(root):
    receipts={}
    for part in ('raw','natural'):
        eq=json.loads((root/part/'equation.json').read_text())
        want=json.loads((root/part/'expanded_polynomial.json').read_text())
        out=defaultdict(int);used=set()
        for row in eq['residuals']:
            r=norm(row)
            for m in r:
                need(len(m)<=2 and all(0<=i<len(eq['variables']) for i in m),'quadratic support')
                used.update(m)
            for m,c in r.items():
                for n,d in r.items():out[tuple(sorted(m+n))]+=c*d
        out={m:c for m,c in out.items() if c}
        need(out==norm(want['terms']),'expanded polynomial mismatch')
        need(used==set(range(len(eq['variables']))),'unused variable')
        need(max(map(len,out))==4,'degree four')
        receipts[part]={'variables':len(eq['variables']),'rows':len(eq['residuals']),
            'monomials':len(out),'coefficient_height':max(map(abs,out.values())),
            'equation_sha256':hashlib.sha256((root/part/'equation.json').read_bytes()).hexdigest(),
            'polynomial_sha256':hashlib.sha256((root/part/'expanded_polynomial.json').read_bytes()).hexdigest()}
    return receipts

def arithmetic():
    counts=defaultdict(int)
    for t in range(12,41):
        H=factorial(t)
        for F in set(range(1,101))|{H-2,H-1,H,H+1,H+2,t*t}:
            V=(F*F+1)**t;B=comb(F*F+t,t)
            need(((V+B-1)//B==F)==(F==H),'fixed point')
            counts['fixed_point_candidates']+=1
        need(2**t>t*t*(t+1),'horizon lower bound')
        need(3*4194304*(t+1)<=2*H,'label exponent bound')
        need(H>2**28 and 28*8388608<2**28 and 2*8388608<=2**28,'majorant base')
        counts['horizon_budgets']+=1
    for t in range(1,13):
        F=factorial(t);ds=[1+F*F//i for i in range(1,t+1)]
        need(prod(ds)==comb(F*F+t,t),'reciprocal product')
        need(all(gcd(x,y)==1 for i,x in enumerate(ds) for y in ds[i+1:]),'coprime moduli')
        counts['reciprocal_products']+=1
    for N in range(2,8):
        for H in range(2,21):
            for K in range(2,8):
                q=(N*H)**K
                need(q%N==0 and q>H**K,'self radix')
                for n in range(H):
                    for j in range(K):
                        need((comb(n,j) if j<=n else 0)<q,'self range coefficients')
                        counts['self_radix_coefficients']+=1
    counts['cap_arithmetic_controls']=ic.arithmetic_controls()
    return dict(counts)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('roots',type=Path,nargs='+');p.add_argument('--output',type=Path)
    a=p.parse_args();out={'status':'passed','variants':{},'arithmetic_controls':arithmetic(),
        'scope':'Literal composition and full polynomial expansion plus finite controls; inherited calculus and unbounded lemmas are not replaced by these checks.'}
    for root in a.roots:out['variants'][root.name]={'cap':semantic(root),'expansion':expansion(root)}
    if a.output:a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
