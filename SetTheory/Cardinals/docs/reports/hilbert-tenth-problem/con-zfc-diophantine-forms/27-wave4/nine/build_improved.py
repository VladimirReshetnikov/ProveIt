#!/usr/bin/env python3
"""Build equivalent, faster nine-variable circuits from pinned Jones specialization.

The upstream constructor is distributed in source/nine/nine_compressor.py.
This file changes only power evaluation and (optionally) radical majorants.
"""
from pathlib import Path
import importlib.util, json, sys
from functools import lru_cache
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'source/nine'))
import nine_compressor as nc
import check_nine as check

def coding_blocks(d, B, nu, keys, z):
    A,M,P,c=d.plus,d.times,d.power,d.const
    # t[j] = B^(5^j), by repeated fifth powers.
    t=[B]
    for _ in range(nu+1):
        t.append(M(P(t[-1],4),t[-1]))
    # v[j]=B^(5^nu-5^j). Reuse fourth powers from t construction.
    v=[None]*(nu+1);v[nu]=c(1)
    for j in range(nu-1,-1,-1):
        v[j]=M(P(t[j],4),v[j+1])
    variables=[t[nu]]+v
    hs=[c(1)]+[c(0)]*4
    for term in variables:
        for deg in range(1,5): hs[deg]=A(hs[deg],M(term,hs[deg-1]))
    baseline=hs[4]
    # Greedy recursive multivariate Horner. Coefficient leaves remain fixed.
    terms=[((4-sum(alpha),)+tuple(alpha),(d.const(name) if isinstance(name,int) else d.fixed(name))) for alpha,name in keys]
    @lru_cache(None)
    def horner(terms):
        if not terms:return c(0)
        positive=[sum(ex[j]>0 for ex,coef in terms) for j in range(len(variables))]
        m=max(positive)
        if m==0:return A(*(coef for ex,coef in terms))
        j=max(range(len(variables)),key=lambda j:(positive[j],sum(ex[j] for ex,coef in terms),j))
        yes=[];no=[]
        for ex,coef in terms:
            if ex[j]:
                ex=list(ex);ex[j]-=1;yes.append((tuple(ex),coef))
            else:no.append((ex,coef))
        return A(horner(tuple(no)),M(variables[j],horner(tuple(yes))))
    e=M(t[nu],A(M(z,baseline),horner(tuple(terms))))
    # S_(5^k)(B)=prod_j S_5(t_j), then S_(4L)=S_L(1+q)(1+q^2).
    factors=[]
    for j in range(nu+1):
        x=t[j]
        factors.append(A(c(1),M(x,A(c(1),x),A(c(1),P(x,2)))))
    q=t[nu+1]
    lam=M(*factors,A(c(1),q),A(c(1),P(q,2)))
    ell=A(*t[1:nu+1])
    return q,ell,lam,e,t[nu]


def make_body(nu, coefficient_keys, weights='majorant', positive=False):
    d = nc.DAG()
    c = d.const
    A, M, S, P = d.plus, d.times, d.minus, d.power
    input_names=['epsilon', 'g0', 'h0', 's0', 'w0', 'phi', 'i0', 'j0', 'n']
    positive_names=['epsilon_plus', 'g', 'h', 's', 'w', 'phi_plus', 'i', 'j', 'n_plus']
    v={name:d.var(positive_names[k] if positive else name) for k,name in enumerate(input_names)}
    z, y = d.fixed('z_index'), d.fixed('y_index')
    b = d.save('b', A(y, v['epsilon']) if positive else A(y, c(1), v['epsilon']))
    g, h, s, w, ii, jj = ((v[key] if positive else A(v[key], c(1))) for key in
                         ['g0', 'h0', 's0', 'w0', 'i0', 'j0'])
    phi=S(v['phi'],c(1)) if positive else v['phi']
    nfinal=S(v['n'],c(1)) if positive else v['n']
    B = d.save('B', P(b, 5))
    L = 5 ** (nu + 1)
    q,ell,lam,e,top=coding_blocks(d,B,nu,coefficient_keys,z)
    for name,val in [('q',q),('ell',ell),('lambda',lam),('e',e)]:d.save(name,val)
    theta = S(B, M(c(2), z))
    N = d.save('N', P(q, 16))
    Gcap = d.save('Gcap', M(c(32), b, top))
    Rleft = A(g, M(e, P(q, 3)), M(ell, P(q, 5)),
              M(A(M(c(2), S(e, M(z, lam)), P(A(c(1), B, g), 4)),
                  M(lam, B), M(lam, B, P(q, 4))), P(q, 7)))
    Rright = A(S(P(q, 3), M(b, ell)), ell, M(theta, lam, P(q, 3)),
               M(S(B, c(2)), P(q, 8)))
    R = d.save('R', A(M(Rleft, S(P(N, 2), N)),
                       M(Rright, S(P(N, 2), c(1)))))
    U = d.save('U', M(P(N, 2), w))
    Y = d.save('Y', M(P(N, 2), s))
    MM = d.save('M', M(R, Y))
    PP = d.save('P', M(c(2), P(MM, 2), U))
    K = d.save('K', A(R, c(1), M(h, S(PP, c(1)))))
    AA = d.save('A', M(MM, A(U, c(1))))
    Bprime = A(M(c(2), R), c(1))
    Wsmall = d.save('Wsmall', M(b, w))
    CC = d.save('C', A(Bprime, Wsmall, phi))
    JJ = d.save('J', S(M(c(4), AA), c(5)))
    QQ = d.save('Q', S(M(c(3), Wsmall, CC), M(c(2), S(P(Wsmall, 2), c(1)))))
    DD = d.save('D', A(M(S(P(AA, 2), c(1)), P(CC, 2)), c(1)))
    EE = d.save('E', M(ii, JJ, DD, P(CC, 2)))
    FF = d.save('F', A(M(S(P(AA, 2), c(1)), P(EE, 2)), c(1)))
    Gp = d.save('Gp', A(AA, M(FF, S(A(M(CC, DD), c(1)), AA))))
    HH = d.save('H', A(Bprime, M(jj, CC)))
    II = d.save('I', A(M(S(P(Gp, 2), c(1)), P(HH, 2)), c(1)))
    a0 = d.save('a0', A(M(S(P(PP, 2), c(1)), P(K, 2)), c(1)))
    a1 = d.save('a1', M(DD, FF, II))
    divisor = d.save('divisor', P(M(JJ, FF), 2))
    dividend = d.save('dividend', P(A(M(QQ, FF), M(JJ, S(HH, CC))), 2))
    margin = d.save('margin', S(S(M(P(K, 2), Gcap),
                               M(c(4), P(S(CC, M(K, Y)), 2), Gcap)),
                             M(c(8), g, P(K, 2))))
    if weights == 'literal':
        V0 = d.save('V0', A(P(a0, 2), c(2)))
        V1 = d.save('V1', A(P(a1, 2), c(2)))
    elif weights == 'majorant':
        V0 = d.save('V0', A(P(PP, 2), P(K, 2), c(2)))
        V1 = d.save('V1', A(M(A(P(AA, 2), P(CC, 2), c(1)),
                              A(P(AA, 2), P(EE, 2), c(1)),
                              A(P(Gp, 2), P(HH, 2), c(1))), c(1)))
    elif weights == 'natural-majorant':
        # Index positivity gives e >= 0 on N; all other leaves here are nonnegative.
        Rl=A(g,M(e,P(q,3)),M(ell,P(q,5)),
             M(A(M(c(2),A(e,M(z,lam)),P(A(c(1),B,g),4)),M(lam,B),M(lam,B,P(q,4))),P(q,7)))
        Rr=A(P(q,3),M(b,ell),ell,M(A(B,M(c(2),z)),lam,P(q,3)),M(A(B,c(2)),P(q,8)))
        Rb=d.save('Rbar',A(M(Rl,A(P(N,2),N)),M(Rr,A(P(N,2),c(1)))))
        Mb=d.save('Mbar',M(Rb,Y))
        Pb=d.save('Pbar',M(c(2),P(Mb,2),U))
        Kb=d.save('Kbar',A(Rb,c(1),M(h,A(Pb,c(1)))))
        Ab=d.save('Abar',M(Mb,A(U,c(1))))
        Bpb=A(M(c(2),Rb),c(1))
        Cb=d.save('Cbar',A(Bpb,Wsmall,phi))
        Jb=A(M(c(4),Ab),c(5))
        Db=d.save('Dbar',A(M(A(P(Ab,2),c(1)),P(Cb,2)),c(1)))
        Eb=d.save('Ebar',M(ii,Jb,Db,P(Cb,2)))
        Fb=d.save('Fbar',A(M(A(P(Ab,2),c(1)),P(Eb,2)),c(1)))
        Gb=d.save('Gpbar',A(Ab,M(Fb,A(M(Cb,Db),c(1),Ab))))
        Hb=d.save('Hbar',A(Bpb,M(jj,Cb)))
        V0=d.save('V0',A(M(A(Pb,c(1)),Kb),c(2)))
        # Factor two makes the degree certificate strictly separated at the final norm.
        V1=d.save('V1',A(M(c(2),A(M(A(Ab,c(1)),Cb),c(1)),
                             A(M(A(Ab,c(1)),Eb),c(1)),A(M(A(Gb,c(1)),Hb),c(1))),c(1)))
    else:
        raise ValueError('Unknown weight choice')
    WW = d.save('W', M(divisor, S(M(c(2), margin), c(1))))
    TT = d.save('T', S(A(M(divisor, nfinal), dividend),
                       M(WW, A(dividend, M(V0, V1)))))
    output = d.save('output', S(P(S(P(TT, 2), M(P(WW, 2), A(a0, M(P(V0, 2), a1)))), 2),
                                  M(c(4), P(WW, 4), P(V0, 2), a0, a1)))
    nodes, root, names = d.prune(output)
    return {'nu': nu, 'L': L, 'weights': weights,
            'variables': positive_names if positive else input_names, 'domain':'positive integers' if positive else 'nonnegative integers', 'nodes': nodes, 'output': root,
            'named_nodes': names,
            'operation_counts': {kind: sum(n['kind'] == kind for n in nodes)
                                 for kind in ['add', 'sub', 'mul']},
            'model': 'Binary +,-,*; fixed coefficients free; all fixed powers expanded.'}

def canonical_coefficients(constants):
    """Fold literal coefficient recipes and alias identical fixed-port polynomials."""
    canonical={};keys=[];aliases={}
    for row in constants['coefficient_records']:
        recipe=row['coefficient_polynomial_in_fixed_ports']
        signature=json.dumps(recipe,sort_keys=True,separators=(',',':'))
        if len(recipe)==1 and not any(recipe[0]['powers']):
            name=recipe[0]['coefficient']
            aliases[row['name']]={'literal':name}
        else:
            name=canonical.setdefault(signature,row['name'])
            aliases[row['name']]={'fixed':name}
        keys.append((tuple(row['alpha']),name))
    return keys,aliases

def run():
    constants=json.loads((ROOT/'source/nine/generated/constants.json').read_text())
    keys=[(tuple(c['alpha']),c['name']) for c in constants['coefficient_records']]
    nu=constants['nu']
    specialized_keys,aliases=canonical_coefficients(constants)
    out=ROOT/'generated';out.mkdir(exist_ok=True)
    ledger={}
    (out/'COEFFICIENT_ALIASES.json').write_text(json.dumps(aliases,indent=2)+'\n')
    for specialized,positive,weight in [(s,p,w) for s in [False,True] for p in [False,True] for w in ['literal','majorant','natural-majorant']]:
        body=make_body(nu,specialized_keys if specialized else keys,weight,positive)
        body['coefficient_recipe_aliases'] = 'COEFFICIENT_ALIASES.json' if specialized else None
        selected=json.loads((ROOT.parent/'INSTANCE.json').read_text())
        body['coefficient_binding']={'instance':'../../INSTANCE.json','tuple_id':selected['tuple_id'],'tuple_sha256':selected['tuple_sha256'],'fixed_leaf_recipe':'../source/nine/generated/constants.json','index_bound_recipe':'../source/nine/generated/index_bound_s.json','warning':'All fixed leaves, z and y are instantiated together, not additional unknowns.'}

        weight += '_specialized' if specialized else ''
        weight += '_positive' if positive else ''
        (out/f'nine_{weight}_dag.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
        head,named=check.diagonal_heads(body)
        ledger[weight]={'operations':sum(body['operation_counts'].values()),'operation_counts':body['operation_counts'],
                        'nodes':len(body['nodes']),'fixed_leaves':sum(n['kind']=='fixed' for n in body['nodes']),'degree':head[0],'leading_coefficient':head[1][()],
                        'named_ledger':named}
    (out/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
    print(json.dumps({k:{j:v for j,v in x.items() if j!='named_ledger'} for k,x in ledger.items()},indent=2))
if __name__=='__main__':run()
