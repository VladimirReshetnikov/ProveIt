#!/usr/bin/env python3
"""Degree-separated source with sparse-borrow and calibrated-popcount Sun10.
No upstream program is imported or executed. All data are fixed and local.
Tail factorizations are elementary identities adapted from source52.
"""
from pathlib import Path
from collections import defaultdict, Counter
from math import prod
import json, hashlib
from circuit import DAG
ROOT = Path(__file__).resolve().parent
VARIABLES = ['f','g','h','k','l','w','x','y','z','m']
KAPPA = 2134940


def source_records(layout):
    src = json.loads((ROOT/'data/parent_quartic31.json').read_text())
    rows = [{tuple(t['powers']): t['coefficient'] for t in row['terms']} for row in src['equations']]
    for dest, source, multiplier in layout['source_row_operations']:
        for mon, co in rows[source-1].items():
            rows[dest-1][mon] = rows[dest-1].get(mon, 0) + multiplier*co
        rows[dest-1] = {mon:co for mon,co in rows[dest-1].items() if co}
    recipes, signatures, blocks = {}, {}, []
    for number, target in zip(layout['order'], layout['targets']):
        grouped = defaultdict(dict)
        for ex, co in sorted(rows[number-1].items()):
            alpha, fixed = ex[:31], ex[31:]
            degree = sum(alpha)
            factor = 2 if degree < 2 or 2 in alpha else 1
            grouped[alpha][fixed] = co*factor
        records = []
        for alpha, recipe in sorted(grouped.items()):
            recipe = tuple(sorted(recipe.items()))
            if len(recipe)==1 and not any(recipe[0][0]):
                ref = {'literal':recipe[0][1]}
            else:
                name = signatures.setdefault(recipe, 'c%03d'%len(signatures))
                recipes[name] = [{'powers':list(ex), 'coefficient':co} for ex,co in recipe]
                ref = {'fixed':name}
            records.append({'alpha':list(alpha), 'degree':sum(alpha), 'coefficient':ref,
                            'recipe':[{'powers':list(ex),'coefficient':co} for ex,co in recipe],
                            'exponent':target-sum(a*w for a,w in zip(alpha,layout['weights']))})
        blocks.append({'source_equation':number,'target':target,'records':records})
    return {'variables':src['variables'],'ports':src['constants'],'blocks':blocks,'recipes':recipes,
            'source_sha256':hashlib.sha256((ROOT/'data/parent_quartic31.json').read_bytes()).hexdigest()}


def horner(d, base, terms):
    terms = sorted(terms, reverse=True)
    previous, result = terms[0]
    for exponent, coefficient in terms[1:]:
        result = d.plus(d.times(result, d.power(base, previous-exponent)), coefficient)
        previous = exponent
    return d.times(result, d.power(base, previous))


def tail(d, v, b, X, Y, cap):
    c,A,M,S,P,N = d.const,d.plus,d.times,d.minus,d.power,d.save
    L=N('L',M(v['l'],Y)); halfU=M(L,X); U=N('U',M(c(2),halfU))
    V=N('V',M(c(4),v['g'],v['w'],Y)); W=N('W',M(b,v['w']))
    halfA=N('halfA',M(halfU,A(V,c(1)))); AA=N('A',M(c(2),halfA))
    BB=N('B1',A(M(c(2),X),c(1))); Am2=S(AA,c(2)); C=N('C',A(BB,M(Am2,v['h'])))
    Phalf=N('Phalf',M(halfU,U,V)); Pn=N('Pn',M(c(2),Phalf)); K=N('K',A(X,c(1),M(v['k'],S(Pn,c(2)))))
    K2=P(K,2); Pn2=P(Pn,2)
    ss=N('S',S(M(c(2),AA),c(5))); tt=N('T',S(M(c(3),W,C),M(c(2),S(P(W,2),c(1)))))
    Q=N('Q',A(M(S(P(Phalf,2),c(1)),K2),c(1))); cap3=P(cap,3); g2=P(v['g'],2)
    diff=N('CKL',S(C,M(K,L)))
    delta=N('Delta',S(M(c(8),cap3,v['g'],K2),M(g2,A(M(c(32),P(diff,2),cap3),M(g2,K2)))))
    O=N('O',delta); xi=N('xi',M(v['z'],v['x']))
    C2=P(C,2); A2m4=S(P(AA,2),c(4)); D=N('D',A(M(A2m4,C2),c(4)))
    E=N('E',M(C2,D,xi)); E2=P(E,2); Fm1=N('Fm1',M(c(4),A2m4,E2)); F=N('F',A(Fm1,c(1)))
    G=N('G',S(M(S(halfA,c(1)),Fm1),c(1))); Omega=N('Omega',M(c(16),E))
    H=N('H',A(C,M(F,A(S(BB,C),M(Omega,v['y'])))))
    I=N('I',A(M(S(P(G,2),c(1)),P(H,2)),c(1)))
    Sigma=N('Sigma',M(xi,P(ss,5))); r=N('t',A(tt,M(ss,v['y']))); ss2=P(ss,2); r2=P(r,2)
    theta=N('Theta',M(S(M(r,S(r2,ss2)),M(ss2,ss)),A(r2,M(c(23),ss2))))
    seed=N('seed',M(b,Q))
    r0=N('r0',A(seed,M(S(M(c(3),O),c(1)),P(M(seed,v['z']),2))))
    r2=N('r2',M(D,F,I))
    center=N('center',S(M(Sigma,v['m']),theta)); sigma2=P(Sigma,2)
    inner=N('norm_inner',S(P(center,2),M(sigma2,A(r0,r2))))
    return N('F10',S(P(inner,2),M(c(4),P(sigma2,2),r0,r2)))



def construct():
    layout=json.loads((ROOT/'data/layout.json').read_text()); records=source_records(layout)
    d=DAG(); c,A,M,S,P,N=d.const,d.plus,d.times,d.minus,d.power,d.save
    v={name:d.var(name) for name in VARIABLES}; W=layout['max_weight']; H=layout['convolution_height']
    b=N('b',A(c(4),M(c(6),v['f']))); v['g']=N('packed_g',M(b,v['g'])); v['h']=N('residue_h',M(b,v['h'])); v['k']=N('residue_k',M(b,A(c(2),M(c(3),v['k'])))); B=N('base',M(d.fixed('beta_source'),P(b,2)))
    ell=N('ell',horner(d,B,[(w,c(1)) for w in layout['weights']]))
    kernels=[]
    for k in range(3):
        terms=[]
        for block in records['blocks']:
            for row in block['records']:
                if row['degree']!=k: continue
                ref=row['coefficient']; node=c(ref['literal']) if 'literal' in ref else d.fixed(ref['fixed'])
                terms.append((row['exponent'],node))
        kernels.append(N('D'+str(k),horner(d,B,terms)))
    packed=N('packed_positive',A(ell,v['g']))
    G=N('Gcode',A(kernels[0],M(packed,A(kernels[1],M(packed,kernels[2])))))
    top=N('top',P(B,W)); N0=N('N0',M(B,top)); N1=N('N1',P(B,H+1)); NN=N('N',M(N0,N1))
    mask=N('mask',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    targets=N('targets',horner(d,B,[(e,c(1)) for e in layout['targets']]))
    T=N('Tcode',A(mask,M(S(B,c(2)),targets,N0)))
    J=N('Jcode',A(M(c(2),G),targets)); Sc=N('Scode',A(v['g'],M(J,N0)))
    X=N('X',A(P(NN,2),M(A(Sc,T),NN),S(S(NN,c(1)),Sc)))
    Hpop=2*W+H+25
    Y=N('Y',M(P(d.fixed('beta_source'),15),d.fixed('beta_mask'),P(B,Hpop-16),b))
    cap=N('Ccap',M(b,top)); out=tail(d,v,b,X,Y,cap)
    nodes,out,names=d.prune(out); degrees=[]
    for node in nodes:
        kind=node['kind']
        degrees.append(1 if kind=='variable' else 0 if kind in ('literal','fixed') else
                       degrees[node['left']]+degrees[node['right']] if kind=='mul' else
                       max(degrees[node['left']],degrees[node['right']]))
    counts=dict(Counter(n['kind'] for n in nodes if 'left' in n))
    body={'schema':'degree-separated-congruence-sun10-v1','domain':'Z','variables':VARIABLES,
          'nodes':nodes,'output':out,'named_nodes':names,'operation_counts':counts,
          'total_operations':sum(counts.values()),'degree_upper_bound':degrees[out],
          'named_degrees':{k:degrees[i] for k,i in names.items()},'beta_exponent':KAPPA,
          'popcount_power':Hpop,'coefficient_tuple':'old31, all four payloads in data/',
          'formal_status':'ordinary mathematical proof; inherited Sun/compiler dependencies; not formal verification'}
    return body,records


def main():
    body,records=construct(); out=ROOT/'generated'; out.mkdir(exist_ok=True)
    (out/'sun10.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
    (out/'source_records.json').write_text(json.dumps(records,indent=2)+'\n')
    metrics={k:v for k,v in body.items() if k not in ('nodes','output','named_nodes')}
    (out/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps({k:body[k] for k in ('total_operations','degree_upper_bound','operation_counts')}))

if __name__=='__main__': main()
