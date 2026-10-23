#!/usr/bin/env python3
"""B2 block source compiler and explicit ten-integer Con(ZFC) polynomial.
New calibrated-mask binomial adapter: 2026-10-23; source compiler adapted from pinned package 43.
Lucas bridge and norm code adapted, with attribution, from ProveIt package31.
Every power has a literal nonnegative integer exponent and is compiled to gates.
"""
from pathlib import Path
from collections import defaultdict
from itertools import combinations_with_replacement, product
from math import comb, factorial
import json, hashlib
from circuit import DAG
ROOT=Path(__file__).resolve().parent
VARIABLES=['f','g','h','k','l','w','x','y','z','m']
BETA_EXPONENT=2134940
PARAMS=json.loads((ROOT/'parameters.json').read_text())
POSITIONS=PARAMS['weights']
def geometric_pair(d, base, n):
    """Return (base^n, sum(base^i, 0<=i<n)) without division."""
    assert n >= 0
    if n == 0:
        return d.const(1), d.const(0)
    if n == 1:
        return base, d.const(1)
    power, total = geometric_pair(d, base, n // 2)
    power2 = d.times(power, power)
    total2 = d.times(total, d.plus(d.const(1), power))
    if n % 2:
        return d.times(power2, base), d.plus(total2, power2)
    return power2, total2


def quadratic_norm(d, X, radicands):
    """Product over all signs of X + sum(sign_i sqrt(radicand_i)).

    Operate in a free rank-2^k algebra with formal r_i^2=radicand_i.
    At each step write an element A+r_i B and replace it by A^2-a_i B^2.
    Exactly k steps leave a scalar. No radicals occur in the emitted circuit.
    """
    count = len(radicands)
    if count == 3:
        # Collected form of the three quadratic norms (35 expanded terms).
        # The verifier proves this identity against all eight signed factors.
        a0, a1, a2 = radicands
        x2 = d.times(X, X)
        v = d.minus(d.minus(d.plus(x2, a2), a0), a1)
        v2 = d.times(v, v)
        four_xa = d.times(d.const(4), x2, a2)
        w = d.minus(d.plus(v2, four_xa), d.times(d.const(4), a0, a1))
        return d.minus(d.times(w, w), d.times(d.const(4), v2, four_xa))
    def ring_square(a):
        result = {}
        items = sorted(a.items())
        for ii, (mask, value) in enumerate(items):
            for jj in range(ii, len(items)):
                mask2, value2 = items[jj]
                term = d.times(value, value2)
                overlap = mask & mask2
                for k in range(count):
                    if overlap & (1 << k):
                        term = d.times(term, radicands[k])
                if ii != jj:
                    term = d.times(d.const(2), term)
                key = mask ^ mask2
                result[key] = d.plus(result.get(key, d.const(0)), term)
        return result

    element = {0: X, **{1 << i: d.const(1) for i in range(count)}}
    for i, radicand in enumerate(radicands):
        bit = 1 << i
        a = {mask: value for mask, value in element.items() if not mask & bit}
        b = {mask ^ bit: value for mask, value in element.items() if mask & bit}
        aa, bb = ring_square(a), ring_square(b)
        element = {}
        for mask in sorted(aa.keys() | bb.keys()):
            value = d.minus(aa.get(mask, d.const(0)),
                            d.times(radicand, bb.get(mask, d.const(0))))
            if d.known.get(value) != 0:
                element[mask] = value
    assert set(element) == {0}
    return element[0]



def source_records():
    source=json.loads((ROOT/'data/parent_quartic31.json').read_text())
    n=len(source['variables']); assert n==31
    blocks=[];recipes={};signatures={}
    for j,eq in enumerate(source['equations']):
        shifted=defaultdict(int)
        for row in eq['terms']:
            ex=row['powers'];supp=[i for i,e in enumerate(ex[:n]) if e]
            for ks in product(*(range(ex[i]+1) for i in supp)):
                powers=[0]*n+ex[n:]; coefficient=row['coefficient']
                for i,k in zip(supp,ks):
                    powers[i]=k;coefficient*=comb(ex[i],k)
                shifted[tuple(powers)]+=coefficient
        grouped=defaultdict(dict)
        for ex,coefficient in sorted(shifted.items()):
            if not coefficient:continue
            alpha=ex[:n];weight=factorial(2-sum(alpha))
            for e in alpha:weight*=factorial(e)
            grouped[alpha][ex[n:]]=coefficient*weight
        records=[]
        for alpha,coeffs in sorted(grouped.items()):
            recipe=tuple(sorted(coeffs.items()))
            if len(recipe)==1 and not any(recipe[0][0]):
                ref={'literal':recipe[0][1]}
            else:
                name=signatures.setdefault(recipe,'c%03d'%len(signatures))
                recipes[name]=[{'powers':list(ex),'coefficient':c} for ex,c in recipe]
                ref={'fixed':name}
            records.append(dict(alpha=list(alpha),coefficient=ref,
                                recipe=[{'powers':list(ex),'coefficient':c} for ex,c in recipe]))
        blocks.append({'source_equation':j+1,'equation':eq['equation'],'records':records})
    # Residual5 has shifted constant +1, ensuring a positive top coefficient.
    lookup={b['source_equation']:b for b in blocks}
    blocks=[lookup[i] for i in PARAMS['order']]
    return dict(variables=source['variables'],ports=source['constants'],
                source_sha256=hashlib.sha256((ROOT/'data/parent_quartic31.json').read_bytes()).hexdigest(),
                blocks=blocks,recipes=recipes)

def construct():
    records=source_records()
    n=31;count=22;maxpos=max(POSITIONS);stride=None
    targets=PARAMS['targets'];Dheight=max(targets);Q=Dheight+2*maxpos
    d=DAG();A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const
    v={name:d.var(name) for name in VARIABLES}
    b=d.save('b',A(c(1),M(c(3),v['f'])))
    base=d.save('base',M(d.fixed('beta_source'),P(b,2)))
    top=d.save('top',P(base,maxpos))
    ell=d.save('ell',A(*(P(base,e) for e in POSITIONS[1:])))
    def sparse_horner(terms):
        terms=sorted(terms,reverse=True)
        prev,result=terms[0]
        for ex,value in terms[1:]:
            result=A(M(result,P(base,prev-ex)),value)
            prev=ex
        return M(result,P(base,prev))
    dterms=[]
    for target,block in zip(targets,records['blocks']):
        for row in block['records']:
            ref=row['coefficient'];coeff=c(ref['literal']) if 'literal' in ref else d.fixed(ref['fixed'])
            exponent=target-sum(w*a for w,a in zip(POSITIONS[1:],row['alpha']))
            assert exponent>=0
            dterms.append((exponent,coeff))
    Dcode=d.save('Dcode',sparse_horner(dterms))
    N0=d.save('N0',M(base,top))
    N1=d.save('N1',P(base,Q+1))
    N=d.save('N',M(N0,N1))
    Mcode=d.save('Mcode',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    target=d.save('target',sparse_horner([(e,c(1)) for e in targets]))
    Tcode=d.save('Tcode',A(Mcode,M(S(base,c(2)),target,N0)))
    Jcode=d.save('Jcode',A(M(c(2),P(A(c(1),v['g']),2),Dcode),target))
    Scode=d.save('Scode',A(v['g'],M(Jcode,N0)))
    # Explicit-mask popcount calibration: no third variable high block.
    X=d.save('X',A(P(N,2),M(A(Scode,Tcode),N),S(S(N,c(1)),Scode)))
    Hpop=(maxpos+Q+2)+maxpos+1+count
    # 2^(1-count) beta^Hpop b^(2Hpop-n), represented without division.
    halfn=(n+1)//2
    Y=d.save('Y',M(P(d.fixed('beta_source'),halfn-1),d.fixed('beta_mask'),
                    P(base,Hpop-halfn),P(b,2*halfn-n)))
    cap=d.save('Ccap',M(b,top))
    merger_degree=5;merged_positivity=True;weight_scheme='structural';adaptive_weights=True
    # Sun 2026, (6.1)--(6.7).
    L = d.save('Lsmall', M(v['l'], Y))
    U = d.save('U', M(c(2), L, X))
    V = d.save('V', M(c(4), v['g'], v['w'], Y))
    W = d.save('Wsmall', M(b, v['w']))
    AA = d.save('A', M(U, A(V, c(1))))
    BB = d.save('Bsmall', A(M(c(2), X), c(1)))
    C = d.save('C', A(BB, M(S(AA, c(2)), v['h'])))
    Pn = d.save('Pn', M(P(U, 2), V))
    K = d.save('K', A(X, c(1), M(v['k'], S(Pn, c(2)))))
    SS = d.save('Ssmall', S(M(c(2), AA), c(5)))
    TT = d.save('Tsmall', S(M(c(3), W, C), M(c(2), S(P(W, 2), c(1)))))
    R2 = d.save('R2', A(M(S(P(Pn, 2), c(4)), P(K, 2)), c(4)))
    cap3 = P(cap, 3)
    Delta = d.save('Delta', S(M(c(8), cap3, v['g'], P(K, 2)),
                            M(P(v['g'], 2), A(M(c(32), P(S(C, M(K, L)), 2), cap3),
                                               M(P(v['g'], 2), P(K, 2))))))
    O0 = d.save('O0', M(P(v['f'], 2), P(v['l'], 2), Delta))

    # Sun 2026, (3.1)--(3.7) and (7.1).
    xi = d.save('xi', M(v['z'], v['x']))
    D = d.save('D', A(M(S(P(AA, 2), c(4)), P(C, 2)), c(4)))
    E = d.save('E', M(P(C, 2), D, xi))
    F = d.save('F', A(M(c(4), S(P(AA, 2), c(4)), P(E, 2)), c(1)))
    Gstar = d.save('Gstar', S(M(c(2), A(AA, c(2)), P(S(AA, c(2)), 2), P(E, 2)), c(1)))
    Omega = d.save('Omega', M(c(16), E))
    Hstar = d.save('Hstar', A(C, M(S(BB, C), F), M(Omega, F, v['y'])))
    Istar = d.save('Istar', A(M(S(P(Gstar, 2), c(1)), P(Hstar, 2)), c(1)))

    Sigma = d.save('Sigma', M(xi, P(SS, merger_degree)))
    r = d.save('merger_argument', A(TT, M(SS, v['y'])))
    SS2 = P(SS, 2)
    if merger_degree == 5:
        Theta = M(S(S(P(r, 3), M(r, SS2)), M(SS2, SS)), A(P(r, 2), M(c(23), SS2)))
    else:
        Theta = M(*(S(P(r, 2), M(c(gamma), SS2)) for gamma in (13, 17, 221)))
    d.save('Theta', Theta)

    # H_k of Sun 2021 (5.4), represented as exact quadratic norms.
    positivity_discriminant = S(M(c(3), O0), c(4))
    if merged_positivity:
        bracket = d.save('positivity_bracket', A(c(1), M(positivity_discriminant, P(b, 2), P(v['z'], 2))))
        radicands = [M(b, bracket), R2, M(D, F, Istar)] if adaptive_weights else [M(b, bracket), M(D, F, Istar), R2]
    else:
        radicands = [b, A(M(positivity_discriminant, P(v['z'], 2)), c(1)), M(D, F, Istar), R2]
    for j, value in enumerate(radicands, 1):
        d.save('A' + str(j), value)
    if weight_scheme == 'structural':
        weight1 = d.save('norm_weight1', radicands[0])
        weight2 = d.save('norm_weight2', M(weight1, A(P(Pn, 2), P(K, 2), c(3))))
        weights = [c(1), weight1, weight2]
    elif adaptive_weights:
        weight1 = d.save('norm_weight1', A(c(1), P(radicands[0], 2)))
        weight2 = d.save('norm_weight2', M(weight1, A(c(1), P(radicands[1], 2))))
        weights = [c(1), weight1, weight2]
    else:
        weight = d.save('norm_weight', A(c(1), *(P(value, 2) for value in radicands)))
        weights = [P(weight, j) for j in range(len(radicands))]
    center = d.save('norm_center', S(M(Sigma, v['m']), Theta))
    Sigma2 = P(Sigma, 2)
    scaled = [d.save('scaled_A' + str(j + 1), M(Sigma2, P(weights[j], 2), value))
              for j, value in enumerate(radicands)]
    out = d.save('F10', quadratic_norm(d, center, scaled))
    nodes,output,names=d.prune(out)
    degree=[]
    for node in nodes:
        if node['kind']=='variable':degree.append(1)
        elif node['kind'] in ('literal','fixed'):degree.append(0)
        else:
            aa,bb=degree[node['left']],degree[node['right']]
            degree.append(aa+bb if node['kind']=='mul' else max(aa,bb))
    body=dict(schema='proveit-selective-borrow-popcount-ten-integer-v1',domain='Z',variables=VARIABLES,
              nodes=nodes,output=output,named_nodes=names,
              operation_counts={k:sum(t['kind']==k for t in nodes) for k in ['add','sub','mul']},
              degree_upper_bound=degree[output],
              named_degrees={k:degree[i] for k,i in names.items()},
              source=dict(positions=POSITIONS,max_position=maxpos,stride=stride,blocks=count,
                          convolution_height=Q,reversal_height=Dheight,targets=targets,order=PARAMS['order'],beta_exponent=BETA_EXPONENT,
                          popcount_power=Hpop,beta_mask_exponent=BETA_EXPONENT+1-count,
                          source_adapter='sparse-borrow-calibrated-mask-popcount'),
              fixed_binding='data/coefficients_binding.json + generated/source_records.json',
              proof='report.pdf',formal_status='ordinary mathematical proof; not proof-assistant checked')
    return body,records

def main():
    body,records=construct()
    outdir=ROOT/'generated';outdir.mkdir(exist_ok=True)
    (outdir/'signed10_b2.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
    (outdir/'source_records.json').write_text(json.dumps(records,indent=2)+'\n')
    metrics={k:body[k] for k in ['variables','operation_counts','degree_upper_bound','source','named_degrees']}
    metrics['total_operations']=sum(body['operation_counts'].values())
    (outdir/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps({k:metrics[k] for k in ['total_operations','degree_upper_bound','source']}))

if __name__=='__main__':main()

