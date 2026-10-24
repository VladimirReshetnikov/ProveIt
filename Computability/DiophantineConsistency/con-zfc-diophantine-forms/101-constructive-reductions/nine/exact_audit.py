#!/usr/bin/env python3
"""Independent source, radical-identity, and exact-degree audit; stdlib only.

No producer or inherited checker is imported. The command takes the nine/
directory of the delivery as its only optional argument.
"""
from collections import defaultdict
from math import comb
from pathlib import Path
import hashlib
import gzip
import math
import json
import sys


def need(ok, text):
    if not ok:
        raise RuntimeError(text)


def load(path):
    return json.loads(path.read_text())


def read_polynomial(path):
    data = load(path)
    result = {}
    for term in data['terms']:
        key = tuple(term['powers'])
        need(key not in result, 'duplicate polynomial monomial')
        need(type(term['coefficient']) is int, 'nonintegral coefficient')
        result[key] = term['coefficient']
    return result


def plus(*polys):
    out = defaultdict(int)
    for poly in polys:
        for exp, value in poly.items():
            out[exp] += value
    return {exp: value for exp, value in out.items() if value}


def scale(poly, value):
    return {exp: value*coefficient for exp, coefficient in poly.items()
            if value*coefficient}


def times(*polys):
    out = {(0, 0, 0, 0): 1}
    for poly in polys:
        acc = defaultdict(int)
        for a, ca in out.items():
            for b, cb in poly.items():
                acc[tuple(x+y for x, y in zip(a, b))] += ca*cb
        out = {exp: value for exp, value in acc.items() if value}
    return out


def power(poly, n):
    return times(*([poly]*n))


def translated(poly, offsets):
    out = poly
    for axis, offset in enumerate(offsets):
        if not offset:
            continue
        acc = defaultdict(int)
        for exp, value in out.items():
            for k in range(exp[axis]+1):
                new = list(exp)
                new[axis] = k
                acc[tuple(new)] += value*comb(exp[axis], k)*offset**(exp[axis]-k)
        out = {exp: value for exp, value in acc.items() if value}
    return out


def degree(poly, weights):
    bound = max(sum(a*b for a, b in zip(exp, weights)) for exp in poly)
    leading = [(exp, value) for exp, value in poly.items()
               if sum(a*b for a, b in zip(exp, weights)) == bound]
    return bound, leading


def source_check(root):
    source = load(root/'data/source.json')
    compact = source['name']=='gapNq85'
    code = load(root/'data/code.json')
    kernels = load(root/'data/kernels.json')
    variables = source['variables']
    weights = code['weights']
    targets = code['targets_by_row']
    n = len(variables)
    need(n == 31 and len(targets) == 22, 'source dimensions')
    need(len(set(weights)) == 31 and min(weights)==0, 'distinct nonnegative weights including zero')
    need(len(set(targets)) == 22, 'distinct targets')
    need(kernels['variables'] == variables, 'kernel variable order')
    target_map = {target: row for row, target in enumerate(targets)}
    actual = [defaultdict(int) for _ in targets]
    interactions = 0
    stored = 0
    coefficient_max_bound = 0
    ports = [int.from_bytes(gzip.decompress((root/'data'/f'{n}.bin.gz').read_bytes()),'little') for n in ['beta','K','MC','MF_source']]
    bits=[v.bit_length() for v in ports]
    bound=864014 if compact else 2134927
    kernel_degrees = []
    for layer in kernels['kernels']:
        d = layer['degree']
        entries = layer['terms']
        need(len({term['exponent'] for term in entries}) == len(entries),
             'duplicate stored kernel location')
        stored += len(entries)
        kernel_degrees.append(max(term['exponent'] for term in entries))
        monomials = []
        if d == 0:
            monomials = [((0,)*n, 0, 1)]
        elif d == 1:
            for p in range(n):
                e=[0]*n;e[p]=1
                monomials.append((tuple(e), weights[p], 1))
        elif d == 2:
            for p in range(n):
                for q in range(p,n):
                    e=[0]*n;e[p]+=1;e[q]+=1
                    monomials.append((tuple(e),weights[p]+weights[q],1 if p==q else 2))
        else:
            raise RuntimeError('source is not quadratic')
        for term in entries:
            coefficient_max_bound=max(coefficient_max_bound,
                abs(sum(t['coefficient']*math.prod(v**p for p,v in zip(t['powers'],ports))
                    for t in term['coefficient'])))
            for e, offset, multiplier in monomials:
                interactions += 1
                row=target_map.get(term['exponent']+offset)
                if row is not None:
                    for term2 in term['coefficient']:
                        actual[row][e+tuple(term2['powers'])] += multiplier*term2['coefficient']
    for row, equation in enumerate(source['equations']):
        expected = defaultdict(int)
        for term in equation['terms']:
            expected[tuple(term['powers'])] += 2*code['row_orientations'][row]*term['coefficient']
        need({e:v for e,v in actual[row].items() if v} ==
             {e:v for e,v in expected.items() if v}, f'exact target identity {row+1}')
    all_one_row = defaultdict(int)
    for term in source['equations'][4]['terms']:
        all_one_row[tuple(term['powers'][n:])] += term['coefficient']
    need({e:v for e,v in all_one_row.items() if v} == {(0,0,0,0):1},
         'all-one source tuple is not a zero')
    need(kernel_degrees == ([1625,1940,1850] if compact else [1406,1726,1636]), 'kernel degrees')
    need(coefficient_max_bound < (1<<bound), 'coefficient magnitude bound')
    W=max(weights)
    H=max(d+d2*W for d2,d in enumerate(kernel_degrees))
    need((W,H,max(targets),stored,interactions)==((115,2080,2048,85,22450) if compact else (115,1866,1834,81,20466)),
         'source height/count tuple')
    # Independently derive every positive-domain threshold exponent.
    kappa=bound+12
    E=H+W+2
    popheight=E+W+23
    lp=(22-popheight*kappa)%2
    delta=(popheight-15)%2
    nB=(popheight-15-delta)//2
    nc=((15+delta)*kappa+lp-22)//2
    need((E,popheight,lp,delta,nB,nc)==((2197,2335,0,0,1160,6480184) if compact else (1983,2121,1,0,1053,16012032)),
         'positive calibration exponents')
    for k in range(50):
        v=kappa+2*k
        u=lp+k+E*v
        popT=(W+23)*v-31*k-22
        logN=nc+delta*k+nB*v
        need(u+popT==2*logN, 'exact symbolic population calibration')
    r=1+2*(E+W+1+H)
    nu=delta+2*nB
    a=r+4*nu+2
    need((r,nu,a)==((8787,2320,18069) if compact else (7931,2106,16357)), 'source and A degrees')
    return dict(identities=22,interactions=interactions,stored_positions=stored,
        W=W,H=H,maximum_target=max(targets),kappa=kappa,Ecode=E,popheight=popheight,
        block_two_power=lp,threshold_b_power=delta,threshold_B_power=nB,
        threshold_two_power=nc,R_degree=r,N_degree=nu,A_degree=a)


def radical_check(root, src):
    one={(0,0,0,0):1}
    A={(1,0,0,0):1};C={(0,1,0,0):1}
    i={(0,0,1,0):1};Z={(0,0,0,1):1}
    delta=plus(power(A,2),scale(one,-1))
    J=plus(scale(A,4),scale(one,-5))
    D=plus(times(delta,C,C),one)
    r=times(i,J,C,C)
    F=plus(times(delta,D,r,r),one)
    G=plus(A,times(F,plus(times(C,D),one,scale(A,-1))))
    HH=plus(C,times(F,Z))
    I=plus(times(plus(power(G,2),scale(one,-1)),HH,HH),one)
    a1=times(D,F,I)
    sigma=scale(times(power(C,5),i),1024)
    P=read_polynomial(root/'data/saturated_corrected_P.json')
    defect=plus(power(P,2),scale(times(sigma,sigma,a1),-1))
    certificate=read_polynomial(root/'data/saturated_corrected_certificate.json')
    shifted=translated(defect,[3,1,1,1])
    need(shifted==certificate,'full exact shifted radical identity')
    need(all(value>0 for value in shifted.values()),'positive radical defect coefficients')
    need(shifted.get((0,0,0,0),0)>0,'strict positive defect constant')
    pshift=translated(P,[3,1,0,0])
    need(all(value>0 for value in pshift.values()),'positive majorant coefficients')
    need(pshift.get((0,0,0,0),0)>0,'strict positive majorant constant')
    a=src['A_degree'];rr=src['R_degree'];W=src['W']
    weight=[a,1,1,rr]
    dP,leadP=degree(P,weight)
    dDef,leadDef=degree(defect,weight)
    need(dP==18*a+rr+30 and len(leadP)==1 and leadP[0][1]>0,
         'exact positive majorant weighted degree')
    need(dDef==18*a+2*rr+60 and len(leadDef)==1 and leadDef[0][1]>0,
         'exact positive radical defect weighted degree')
    dOmega=5*a+2*W+3
    dE=a+4
    dV0=3*a+rr+1
    dd0=3*a+rr+2
    da0=2*dV0
    small_terms=[2*dE,dE+dOmega+dV0,dE+dOmega+dP,
                 2*dOmega+dd0,2*dOmega+dDef]
    dsmall=max(small_terms)
    need(small_terms.count(dsmall)==1 and dsmall==2*dOmega+dDef,
         'unique positive Bsmall leader')
    outer_terms=[2*dsmall,2*dOmega+dV0+dP+dsmall,
                 4*dOmega+dd0+2*dP,4*dOmega+da0+dDef]
    final_degree=max(outer_terms)
    need(outer_terms.count(final_degree)==1 and outer_terms.index(final_degree)==1,
         'unique final norm leader')
    need(final_degree==59*a+4*rr+8*W+103==997810,'final degree')
    # Check the numerical metadata of the delivered circuit, without importing
    # its builder or using those numbers in the proof above.
    graph=load(root/'equations/boundary_complete.json')
    need(graph['exact_degree']==final_degree and graph['source_degree']==src['R_degree']
         and graph['A_degree']==src['A_degree']
         and graph['threshold_degree']==src['N_degree'], 'delivered degree metadata')
    need(graph['threshold_scale_exponent']==src['threshold_two_power']
         and graph['threshold_B_power']==src['threshold_B_power']
         and graph['threshold_b_power']==src['threshold_b_power']
         and graph['block_scale_power_of_two']==src['block_two_power'],
         'delivered threshold metadata')
    return dict(local_radicand_terms=len(a1),local_majorant_terms=len(P),
        local_defect_terms=len(defect),shifted_defect_terms=len(shifted),
        positive_defect_constant=shifted[(0,0,0,0)],
        majorant_weighted_degree=dP,majorant_leading=leadP,
        defect_weighted_degree=dDef,defect_leading=leadDef,
        norm_term_degrees=outer_terms,exact_degree=final_degree,
        proof_of_attainment='Each relevant leading coefficient is positive; the maximum is unique.')


def main():
    root=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent
    src=source_check(root)
    print('Exact source and positive threshold checks PASS',flush=True)
    rad=radical_check(root,src)
    compact=source_check(root/'compact')
    result=dict(status='PASS',source=src,compact_source=compact,radical_and_degree=rad,
        scope='Exact finite algebra and source calibration arithmetic, with ordinary unbounded semantic dependencies stated in the adjacent audit.',
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (Path(__file__).parent/'EXACT_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
