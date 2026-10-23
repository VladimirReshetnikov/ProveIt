#!/usr/bin/env python3
"""Shared kernel taps composed with the unchanged package59 Sun finalizer.

Each coalesced coefficient is inserted exactly once. Fixed ports are the
complete old31 tuple. Standard library only; see PROOF.md and NOTICE.md.
"""
from pathlib import Path
from collections import Counter
import hashlib,json
from circuit import DAG
from tail import tail

ROOT=Path(__file__).resolve().parent
VARIABLES=['f','g','h','k','l','w','x','y','z','m']
KAPPA=2134940

def horner(d,base,terms):
    terms=sorted(terms,reverse=True)
    previous,result=terms[0]
    for exponent,coefficient in terms[1:]:
        result=d.plus(d.times(result,d.power(base,previous-exponent)),coefficient)
        previous=exponent
    return d.times(result,d.power(base,previous))

def construct():
    layout=json.loads((ROOT/'data/layout.json').read_text())
    source=json.loads((ROOT/'data/kernels.json').read_text())
    d=DAG();c,A,M,S,P,N=d.const,d.plus,d.times,d.minus,d.power,d.save
    v={name:d.var(name) for name in VARIABLES}
    W=layout['max_weight'];H=layout['convolution_height']
    b=N('b',A(c(1),M(c(3),v['f'])))
    B=N('base',M(d.fixed('beta_source'),P(b,2)))
    ell=N('ell',horner(d,B,[(w,c(1)) for w in layout['weights']]))
    recipes={};byrecipe={};kernels=[]
    for degree,layer in enumerate(source['kernels']):
        if layer['degree']!=degree:raise ValueError('kernel degree order')
        terms=[];seen=set()
        for row in layer['terms']:
            e=row['exponent']
            if e in seen:raise ValueError('duplicate coalesced kernel position')
            seen.add(e);rec=row['coefficient'];key=json.dumps(rec,sort_keys=True)
            if key not in byrecipe:
                name='c%03d'%len(byrecipe);byrecipe[key]=name;recipes[name]=rec
            name=byrecipe[key]
            node=c(rec[0]['coefficient']) if len(rec)==1 and not any(rec[0]['powers']) else d.fixed(name)
            terms.append((e,node))
        kernels.append(N('D'+str(degree),horner(d,B,terms)))
    packed=N('packed_positive',A(ell,v['g']))
    G=N('Gcode',A(kernels[0],M(packed,A(kernels[1],M(packed,kernels[2])))))
    top=N('top',P(B,W));N0=N('N0',M(B,top));N1=N('N1',P(B,H+1));NN=N('N',M(N0,N1))
    mask=N('mask',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    targets=N('targets',horner(d,B,[(e,c(1)) for e in layout['targets']]))
    Tc=N('Tcode',A(mask,M(S(B,c(2)),targets,N0)))
    Jc=N('Jcode',A(M(c(2),G),targets));Sc=N('Scode',A(v['g'],M(Jc,N0)))
    X=N('X',A(P(NN,2),M(A(Sc,Tc),NN),S(S(NN,c(1)),Sc)))
    Hpop=2*W+H+25
    Y=N('Y',M(P(d.fixed('beta_source'),15),d.fixed('beta_mask'),P(B,Hpop-16),b))
    cap=N('Ccap',M(b,top));out=tail(d,v,b,X,Y,cap)
    nodes,out,names=d.prune(out);degrees=[]
    for node in nodes:
        kind=node['kind']
        degrees.append(1 if kind=='variable' else 0 if kind in ('literal','fixed') else
                       degrees[node['left']]+degrees[node['right']] if kind=='mul' else
                       max(degrees[node['left']],degrees[node['right']]))
    counts=dict(Counter(n['kind'] for n in nodes if 'left' in n))
    body={'schema':'shared-taps-sun10-v1','domain':'Z','variables':VARIABLES,
          'nodes':nodes,'output':out,'named_nodes':names,
          'operation_counts':counts,'total_operations':sum(counts.values()),
          'degree_upper_bound':degrees[out],
          'named_degrees':{k:degrees[i] for k,i in names.items()},
          'base_scale_exponent':KAPPA,'mask_scale_exponent':KAPPA-21,
          'popcount_power':Hpop,'W':W,'Hcode':H,'Qcode':max(layout['targets']),
          'coefficient_recipes':recipes,'coefficient_tuple':'complete old31 tuple',
          'source_syntax_sha256':hashlib.sha256((ROOT/'data/source_system65.json').read_bytes()).hexdigest(),
          'kernel_sha256':hashlib.sha256((ROOT/'data/kernels.json').read_bytes()).hexdigest(),
          'formal_status':'ordinary mathematical proof; inherited Sun/compiler dependencies; not formal verification'}
    return body

def main():
    out=ROOT/'generated';out.mkdir(exist_ok=True);body=construct()
    (out/'sun10.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
    metrics={k:v for k,v in body.items() if k not in ('nodes','output','named_nodes','coefficient_recipes')}
    (out/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps({k:body[k] for k in ('total_operations','degree_upper_bound','operation_counts')}))

if __name__=='__main__':main()
