#!/usr/bin/env python3
"""Explicit ten-integer Con(ZFC) polynomial with two-root congruence finalizer.
The inherited selective source is retargeted for its unshifted 94-record form.
Lucas bridge adapted, with attribution, from ProveIt package31 and Sun.
Every power has a literal nonnegative integer exponent and is compiled to gates.
"""
from pathlib import Path
from collections import defaultdict
from math import factorial
import json, hashlib
from circuit import DAG
ROOT=Path(__file__).resolve().parent
VARIABLES=['f','g','h','k','l','w','x','y','z','m']
BETA_EXPONENT=2134940
PARAMS=json.loads((ROOT/'code_positive.json').read_text())
POSITIONS=PARAMS['weights']
def source_records():
    source=json.loads((ROOT/'data/parent_quartic31.json').read_text())
    n=len(source['variables']); assert n==31
    blocks=[];recipes={};signatures={}
    for j,eq in enumerate(source['equations']):
        shifted=defaultdict(int)
        for row in eq['terms']:
            shifted[tuple(row['powers'])]+=row['coefficient']
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
    # Unshifted residual5 has leading reversed coefficient +1 at target minus w_E.
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
    # Recover old_f=2*f+1 in the proof; only b is needed in the polynomial.
    b=d.save('b',A(M(c(6),v['f']),c(4)))
    v['g']=d.save('packed_g',M(b,v['g']))
    v['h']=d.save('residue_h',M(b,v['h']))
    v['k']=d.save('residue_k',M(b,A(M(c(3),v['k']),c(2))))
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
    Jcode=d.save('Jcode',A(M(c(2),P(A(c(1),ell,v['g']),2),Dcode),target))
    Scode=d.save('Scode',A(v['g'],M(Jcode,N0)))
    # Explicit-mask popcount calibration: no third variable high block.
    X=d.save('X',A(P(N,2),M(A(Scode,Tcode),N),S(S(N,c(1)),Scode)))
    Hpop=(maxpos+Q+2)+maxpos+1+count
    # 2^(1-count) beta^Hpop b^(2Hpop-n), represented without division.
    halfn=(n+1)//2
    Y=d.save('Y',M(P(d.fixed('beta_source'),halfn-1),d.fixed('beta_mask'),
                    P(base,Hpop-halfn),P(b,2*halfn-n)))
    cap=d.save('Ccap',M(b,top))
    merger_degree=5
    # Sun 2026, (6.1)--(6.7).
    L = d.save('Lsmall', M(v['l'], Y))
    Uhalf=d.save('Uhalf',M(L,X))
    U = d.save('U', M(c(2), Uhalf))
    V = d.save('V', M(c(4), v['g'], v['w'], Y))
    W = d.save('Wsmall', M(b, v['w']))
    AA = d.save('A', M(U, A(V, c(1))))
    BB = d.save('Bsmall', A(M(c(2), X), c(1)))
    C = d.save('C', A(BB, M(S(AA, c(2)), v['h'])))
    Phalf=d.save('Phalf',M(Uhalf,U,V))
    Pn = d.save('Pn',M(c(2),Phalf))
    K = d.save('K', A(X, c(1), M(v['k'], S(Pn, c(2)))))
    SS = d.save('Ssmall', S(M(c(2), AA), c(5)))
    TT = d.save('Tsmall', S(M(c(3), W, C), M(c(2), S(P(W, 2), c(1)))))
    Q2=d.save('Q2',A(M(S(P(Phalf,2),c(1)),P(K,2)),c(1)))
    cap3 = P(cap, 3)
    Delta = d.save('Delta', S(M(c(8), cap3, v['g'], P(K, 2)),
                            M(P(v['g'], 2), A(M(c(32), P(S(C, M(K, L)), 2), cap3),
                                               M(P(v['g'], 2), P(K, 2))))))
    O0 = d.save('O0', Delta)  # The seed forces l != 0; old_f is always odd.

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

    # The finalizer forces b and Q2 to be squares; a/b is odd and r1/b even.
    positivity_discriminant = S(M(c(3), O0), c(1))
    seed=d.save('seed',M(b,Q2))
    r0=d.save('r0',A(seed,M(positivity_discriminant,P(M(seed,v['z']),2))))
    r1=d.save('r1',M(D,F,Istar))
    center=d.save('norm_center',S(M(Sigma,v['m']),Theta))
    sigma2=P(Sigma,2)
    inner=d.save('norm_inner',S(P(center,2),M(sigma2,A(r0,r1))))
    out=d.save('F10',S(P(inner,2),M(c(4),P(sigma2,2),r0,r1)))
    nodes,output,names=d.prune(out)
    degree=[]
    for node in nodes:
        if node['kind']=='variable':degree.append(1)
        elif node['kind'] in ('literal','fixed'):degree.append(0)
        else:
            aa,bb=degree[node['left']],degree[node['right']]
            degree.append(aa+bb if node['kind']=='mul' else max(aa,bb))
    body=dict(schema='proveit-two-root-congruence-ten-integer-v1',domain='Z',variables=VARIABLES,
              nodes=nodes,output=output,named_nodes=names,
              operation_counts={k:sum(t['kind']==k for t in nodes) for k in ['add','sub','mul']},
              degree_upper_bound=degree[output],
              named_degrees={k:degree[i] for k,i in names.items()},
              source=dict(positions=POSITIONS,max_position=maxpos,stride=stride,blocks=count,
                          convolution_height=Q,reversal_height=Dheight,targets=targets,order=PARAMS['order'],beta_exponent=BETA_EXPONENT,
                          popcount_power=Hpop,beta_mask_exponent=BETA_EXPONENT+1-count,
                          source_adapter='sparse-borrow-calibrated-mask-popcount'),
              fixed_binding='data/coefficients_binding.json + generated/source_records.json',
              proof='PROOF.md',formal_status='ordinary mathematical proof; not proof-assistant checked')
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

