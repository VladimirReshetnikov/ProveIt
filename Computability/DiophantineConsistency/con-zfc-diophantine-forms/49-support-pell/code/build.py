#!/usr/bin/env python3
"""Build the literal ten-integer polynomial with a quadratic-system source.

Only Python's standard library is required. The old Sun finalizer is retained
with attribution; the source is the new multi-target quadratic packing.
"""
from __future__ import annotations
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
from functools import lru_cache
from circuit import DAG
from parent_arithmetic import add, mul, shift_positive

ROOT = Path(__file__).resolve().parents[1]
VARIABLES = ['f','g','h','k','l','w','x','y','z','m']
PORTS = ['beta','K0','MC','MF']
PORT_FILES = ['beta','K','MC','MF_source']
ROW_ORDER = list(range(4)) + list(range(5,22)) + [4]
# A transparent uniform bound: each port < 2^1070004, their sum+1
# < 2^1070007, H=8*(1+sum ports)^2 < 2^2140017.
# 4*33^2 < 2^13; beta_source=2^2140030 is an even power of two.
BETA_EXPONENT = 2140030


def read_ports():
    return {name:int.from_bytes(gzip.decompress(
        (ROOT/'coefficients/payloads'/f'{file}.bin.gz').read_bytes()),'little')
        for name,file in zip(PORTS,PORT_FILES)}


def parent_rows():
    data=json.loads((ROOT/'upstream/parent_system.json').read_text())
    names=data['variables']+data['constants']; n=len(data['variables'])
    z=(0,)*len(names)
    env={}
    for i,name in enumerate(names):
        ex=list(z);ex[i]=1;env[name]={tuple(ex):1}
    def read(v):return ({z:v} if v else {}) if isinstance(v,int) else env[v]
    for name,op,a,b in data['source']:
        env[name]=mul(read(a),read(b)) if op=='*' else add(read(a),read(b),-1 if op=='-' else 1)
    raw=[shift_positive(add(read(a),read(b),-1),n) for a,b in data['comparisons']]
    assert len(raw)==22 and n==31
    return [raw[i] for i in ROW_ORDER],data['variables']


def coefficient_data():
    rows,names=parent_rows(); records=[]; aliases={}; recipes={}; n=len(names)
    for j,row in enumerate(rows):
        grouped={}
        for mon,coef in row.items():
            alpha,ports=mon[:n],mon[n:]
            d=sum(alpha);assert d<=2
            multiplier=math.factorial(2-d)*math.prod(math.factorial(x) for x in alpha)
            grouped.setdefault(alpha,{})[ports]=coef*multiplier
        rec=[]
        for alpha,poly in sorted(grouped.items()):
            poly={p:c for p,c in poly.items() if c}
            signature=tuple(sorted(poly.items()))
            if len(signature)==1 and not any(signature[0][0]):
                leaf=signature[0][1]; sign=1
            else:
                sign=1 if signature[0][1]>0 else -1
                signature=tuple((p,c*sign) for p,c in signature)
                if signature not in aliases:
                    name=f'c{len(aliases):03d}'
                    aliases[signature]=name
                    recipes[name]=[{'powers':list(p),'coefficient':c} for p,c in signature]
                leaf=aliases[signature]
            rec.append({'alpha':list(alpha),'leaf':leaf,'sign':sign})
        records.append(rec)
    return {'variables':names,'ports':PORTS,'row_order_one_based':[i+1 for i in ROW_ORDER],
            'rows':records,'recipes':recipes,'beta_source_exponent':BETA_EXPONENT}


def evaluate_recipe(recipe,ports,modulus=None):
    total=0
    for row in recipe:
        term=row['coefficient']
        for name,power in zip(PORTS,row['powers']):
            term*=pow(ports[name],power,modulus) if modulus else ports[name]**power
            if modulus:term%=modulus
        total+=term
    return total%modulus if modulus else total


def fixed_values(data,modulus):
    ports=read_ports()
    result={name:evaluate_recipe(poly,ports,modulus) for name,poly in data['recipes'].items()}
    result['beta_source']=pow(2,BETA_EXPONENT,modulus)
    return result


def geometric_pair(d,base,n):
    if n==0:return d.const(1),d.const(0)
    if n==1:return base,d.const(1)
    p,s=geometric_pair(d,base,n//2)
    p2=d.times(p,p);s2=d.times(s,d.plus(d.const(1),p))
    return (d.times(p2,base),d.plus(s2,p2)) if n%2 else (p2,s2)


def quadratic_form(d,terms,coordinates):
    """Shared multivariate Horner evaluation, with a fixed degree of two."""
    @lru_cache(None)
    def go(items):
        if not items:return d.const(0)
        counts=[sum(ex[j]>0 for ex,co in items) for j in range(len(coordinates))]
        if not max(counts):return d.plus(*(co for ex,co in items))
        j=max(range(len(coordinates)),key=lambda j:(counts[j],sum(ex[j] for ex,co in items),j))
        yes=[];no=[]
        for ex,co in items:
            if ex[j]:
                e=list(ex);e[j]-=1;yes.append((tuple(e),co))
            else:no.append((ex,co))
        return d.plus(go(tuple(no)),d.times(coordinates[j],go(tuple(yes))))
    return go(tuple(terms))


def construct():
    data=coefficient_data()
    weights=json.loads((ROOT/'data/weights.json').read_text())['weights']
    t=max(weights);targets=[2*t+j*(2*t+1) for j in range(22)]
    span=targets[-1]+2*t
    d=DAG();A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const
    v={name:d.var(name) for name in VARIABLES}
    b=d.save('b',A(c(1),M(c(3),v['f'])))
    base=d.save('base',M(d.fixed('beta_source'),P(b,2)))
    top=d.save('top',P(base,t))
    coords=[top]+[P(base,t-w) for w in weights[1:]]
    rowforms=[]
    for row in data['rows']:
        terms=[]
        for term in row:
            ex=(2-sum(term['alpha']),)+tuple(term['alpha'])
            leaf=c(term['leaf']) if isinstance(term['leaf'],int) else d.fixed(term['leaf'])
            if term['sign']==-1:leaf=M(c(-1),leaf)
            terms.append((ex,leaf))
        rowforms.append(quadratic_form(d,terms,coords))
    step=d.save('block_step',P(base,2*t+1))
    dcode=rowforms[-1]
    for form in reversed(rowforms[:-1]):dcode=A(form,M(step,dcode))
    Dcode=d.save('Dcode',dcode)
    ell=d.save('ell',A(*(P(base,w) for w in weights[1:])))
    N0=d.save('N0',M(top,base))
    endpower,geosum=geometric_pair(d,base,span+1)
    N1=d.save('N1',M(c(4),endpower))
    N=d.save('N',M(N0,N1))
    _,blocks=geometric_pair(d,step,22)
    targetsum=d.save('targetsum',M(P(top,2),blocks))
    target=d.save('target',M(S(base,c(2)),targetsum))
    mask=d.save('mask',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    Tcode=d.save('Tcode',A(mask,M(target,N0)))
    Jcode=d.save('Jcode',A(M(c(2),P(A(c(1),v['g']),2),Dcode),M(base,geosum)))
    Scode=d.save('Scode',A(v['g'],M(Jcode,N0)))
    Rcode=d.save('Rcode',A(M(A(Scode,Tcode,c(1)),N),Tcode,c(1)))
    X=d.save('X',M(S(N,c(1)),Rcode))
    Y=d.save('Y',P(N,2))
    cap=d.save('Ccap',M(b,top))

    # Sun 2026 (6.1)--(6.7), followed by the package-31 finalizer.
    L=d.save('Lsmall',M(v['l'],Y))
    U=d.save('U',M(c(2),L,X))
    V=d.save('V',M(c(4),v['g'],v['w'],Y))
    W=d.save('Wsmall',M(b,v['w']))
    AA=d.save('A',M(U,A(V,c(1))))
    BB=d.save('Bsmall',A(M(c(2),X),c(1)))
    C=d.save('C',A(BB,M(S(AA,c(2)),v['h'])))
    Pn=d.save('Pn',M(P(U,2),V))
    K=d.save('K',A(X,c(1),M(v['k'],S(Pn,c(2)))))
    SS=d.save('Ssmall',S(M(c(2),AA),c(5)))
    TT=d.save('Tsmall',S(M(c(3),W,C),M(c(2),S(P(W,2),c(1)))))
    R2=d.save('R2',A(M(S(P(Pn,2),c(4)),P(K,2)),c(4)))
    cap3=P(cap,3)
    Delta=d.save('Delta',S(M(c(8),cap3,v['g'],P(K,2)),
        M(P(v['g'],2),A(M(c(32),P(S(C,M(K,L)),2),cap3),M(P(v['g'],2),P(K,2))))))
    O=d.save('O',M(P(v['f'],2),P(v['l'],2),Delta))
    xi=d.save('xi',M(v['z'],v['x']))
    D=d.save('D',A(M(S(P(AA,2),c(4)),P(C,2)),c(4)))
    E=d.save('E',M(P(C,2),D,xi))
    F=d.save('F',A(M(c(4),S(P(AA,2),c(4)),P(E,2)),c(1)))
    Gstar=d.save('Gstar',S(M(c(2),A(AA,c(2)),P(S(AA,c(2)),2),P(E,2)),c(1)))
    Omega=d.save('Omega',M(c(16),E))
    Hstar=d.save('Hstar',A(C,M(S(BB,C),F),M(Omega,F,v['y'])))
    Istar=d.save('Istar',A(M(S(P(Gstar,2),c(1)),P(Hstar,2)),c(1)))
    Sigma=d.save('Sigma',M(xi,P(SS,5)))
    r=d.save('merger_argument',A(TT,M(SS,v['y'])))
    ss2=P(SS,2)
    Theta=d.save('Theta',M(S(S(P(r,3),M(r,ss2)),M(ss2,SS)),A(P(r,2),M(c(23),ss2))))
    r0=d.save('r0',M(b,A(c(1),M(S(M(c(3),O),c(4)),P(b,2),P(v['z'],2)))))
    r1=d.save('r1',R2)
    r2=d.save('r2',M(D,F,Istar))
    w1=d.save('weight1',r0)
    w2=d.save('weight2',M(w1,A(P(Pn,2),P(K,2),c(3))))
    center=d.save('center',S(M(Sigma,v['m']),Theta))
    sigma2=P(Sigma,2)
    a0=d.save('a0',M(sigma2,r0))
    a1=d.save('a1',M(sigma2,P(w1,2),r1))
    a2=d.save('a2',M(sigma2,P(w2,2),r2))
    x2=P(center,2)
    vn=d.save('Vnorm',S(S(A(x2,a2),a0),a1))
    vn2=P(vn,2)
    xa4=M(c(4),x2,a2)
    wn=d.save('Wnorm',S(A(vn2,xa4),M(c(4),a0,a1)))
    out=d.save('F10',S(P(wn,2),M(c(4),vn2,xa4)))
    nodes,output,names=d.prune(out)
    deg=[]
    for node in nodes:
        k=node['kind']
        if k=='variable':deg.append(1)
        elif k in ('fixed','literal'):deg.append(0)
        else:
            da,db=deg[node['left']],deg[node['right']]
            deg.append(da+db if k=='mul' else max(da,db))
    body={'schema':'proveit-support-separated-signed10-v1','domain':'integers',
          'variables':VARIABLES,'nodes':nodes,'output':output,'named_nodes':names,
          'degree_upper_bound':deg[output],
          'named_degree_upper_bounds':{name:deg[i] for name,i in names.items()},
          'operation_counts':{k:sum(node['kind']==k for node in nodes) for k in ['add','sub','mul']},
          'source_parameters':{'maximum_weight':t,'targets':targets,'span':span,'beta_exponent':BETA_EXPONENT},
          'artifact_paths_relative_to':'this_json_file',
          'coefficient_binding':'coefficient_recipes.json',
          'native_coefficient_binding':'../coefficients/COEFFICIENT_BINDING.json',
          'fixed_leaf_binding':'../fixed/FIXED_LEAVES.json',
          'proof':'../sections/ten.tex',
          'counting':'Each binary addition, subtraction and multiplication is one operation; constant leaves, constant-only arithmetic and reuse are free. Fixed powers are expanded.'}
    return body,data


def degree_certificate(body,data,prime=1000000007):
    fixed=fixed_values(data,prime)
    degrees=[];leads=[]
    # This is the exact coefficient at each propagated degree bound after
    # substituting every variable by T, reduced modulo the stated prime.
    for node in body['nodes']:
        kind=node['kind']
        if kind=='variable':degree,lead=1,1
        elif kind=='literal':degree,lead=0,node['value']%prime
        elif kind=='fixed':degree,lead=0,fixed[node['name']]
        else:
            a,b=node['left'],node['right']
            if kind=='mul':degree,lead=degrees[a]+degrees[b],leads[a]*leads[b]%prime
            else:
                degree=max(degrees[a],degrees[b])
                va=leads[a] if degrees[a]==degree else 0
                vb=leads[b] if degrees[b]==degree else 0
                lead=(va+vb if kind=='add' else va-vb)%prime
        degrees.append(degree);leads.append(lead)
    i=body['output'];assert leads[i]!=0
    return {'status':'PASS','method':'Nonzero coefficient at the total-degree upper bound after all ten variables are set equal to T, modulo a prime. This is an exact lower-bound certificate, not random testing.',
            'prime':prime,'degree':degrees[i],'leading_coefficient_mod_prime':leads[i],
            'all_variable_slopes':1,'named_certificates':{n:{'degree_bound':degrees[j],'leading_coefficient':leads[j]} for n,j in body['named_nodes'].items()}}


def main():
    body,data=construct()
    ports=read_ports()
    H=8*(1+sum(ports.values()))**2
    assert (1<<BETA_EXPONENT)>4*33**2*H
    assert BETA_EXPONENT%2==0
    bound={'status':'PASS','ordinary_coefficient_bound':'8*(1+beta+K0+MC+MF)^2',
           'coefficient_L1_bound':8,'maximum_port_degree':2,'H_bit_length':H.bit_length(),
           'beta_exponent':BETA_EXPONENT,'required_lower_bound_bit_length':(4*33**2*H).bit_length(),
           'strict_beta_inequality':True,'port_bit_lengths':{name:value.bit_length() for name,value in ports.items()}}
    degree=degree_certificate(body,data)
    body['exact_degree']=degree['degree']
    for name,obj in [('data/polynomial.json',body),('data/coefficient_recipes.json',data),
                     ('certificates/coefficient_bound.json',bound),('certificates/degree.json',degree)]:
        (ROOT/name).write_text(json.dumps(obj,indent=2)+'\n')
    summary={'variables':len(VARIABLES),'degree':body['exact_degree'],
             'operations':sum(body['operation_counts'].values()),'operation_counts':body['operation_counts'],
             'fixed_nonliteral_leaves':sum(n['kind']=='fixed' for n in body['nodes']),
             'weighted_coefficients':sum(len(r) for r in data['rows']),
             'degree_reduction_factor_vs_package31':(126496*5**31+27064)/body['exact_degree']}
    (ROOT/'certificates/metrics.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    if not __debug__: raise SystemExit('Run without -O: checks are required.')
    main()

