#!/usr/bin/env python3
"""Direct multi-target quadratic coding into the 10-integer Sun finalizer.

New: B2 weights, all quadratic residuals encoded without forming their SOS,
and simultaneous carry targets. The downstream Lucas and norm formulas are
adapted unchanged from ProveIt package 31 (source attribution in README).
"""
from pathlib import Path
from itertools import product, combinations_with_replacement
from math import comb, factorial
from functools import lru_cache
import json, hashlib, sys
ROOT=Path(__file__).resolve().parent
UP=ROOT.parent
from circuit import DAG
from finalizer_tools import geometric_pair, quadratic_norm
PARENT=UP/'data/parent_quartic31.json'
VARIABLES=['f','g','h','k','l','w','x','y','z','m']


def weights():
    n=1023; primitive=(1<<10)|(1<<3)|1
    powers=[];x=1
    for _ in range(n):
        powers.append(x);x<<=1
        if x&1024:x^=primitive
    if x!=1 or len(set(powers))!=n:raise ValueError('primitive field check failed')
    logs={v:k for k,v in enumerate(powers)}
    sub={0,*[powers[33*j] for j in range(31)]}
    aa=sorted(logs[2^v] for v in sub)
    gap,i=max(((aa[(i+1)%32]-aa[i])%n,i) for i in range(32))
    origin=aa[(i+1)%32]
    ww=sorted((x-origin)%n for x in aa)
    ss=[sum(p) for p in combinations_with_replacement(ww,2)]
    assert len(set(ss))==len(ss)==528
    return ww,dict(field_polynomial='x^10+x^3+1',field_size=1024,
                   primitive_generator=2,log_origin=origin,largest_gap=gap,
                   weights_including_zero=ww,B2_sums_checked=528)


def shifted_residuals():
    obj=json.loads(PARENT.read_text());n=len(obj['variables'])
    out=[]
    for eq in obj['equations']:
        shifted={}
        for row in eq['terms']:
            e=row['powers']
            for ex in product(*(range(e[j]+1) for j in range(n))):
                c=row['coefficient']
                for j in range(n):c*=comb(e[j],ex[j])
                key=tuple(ex)+tuple(e[n:])
                shifted[key]=shifted.get(key,0)+c
        shifted={key:c for key,c in shifted.items() if c}
        out.append((eq['number'],shifted))
    # Last channel's constant is +1, making D(B)>0 for sufficiently large B.
    fifth=out.pop(4);assert fifth[0]==5
    assert {k[n:]:c for k,c in fifth[1].items() if not any(k[:n])}=={(0,0,0,0):1}
    out.append(fifth)
    assert all(sum(e[:n])<=2 for _,rows in out for e in rows)
    return obj,out


def canonical_residual_coefficients(obj,rs):
    n=len(obj['variables']);recipes={};sig_names={};norms=[];ordinary=[]
    for j,rows in rs:
        rr={}
        for ex,c in rows.items():rr.setdefault(ex[:n],{})[ex[n:]]=c
        ordinary.append(rr)
        rec=[]
        for alpha,co in sorted(rr.items()):
            mul=factorial(2-sum(alpha))
            for ai in alpha:mul*=factorial(ai)
            sig=tuple(sorted((ee,cc*mul) for ee,cc in co.items()))
            if len(sig)==1 and not any(sig[0][0]):name=sig[0][1]
            else:
                name=sig_names.get(sig)
                if name is None:
                    name='c%03d'%len(sig_names);sig_names[sig]=name
                    recipes[name]=[dict(powers=list(e),coefficient=c) for e,c in sig]
            rec.append((alpha,name))
        norms.append((j,rec))
    # Symbolic interval bound using already audited bit lengths of native tuple.
    binding=json.loads((UP/'data/native_coefficients_binding.json').read_text())
    bb={ {'K':'K0','MF_source':'MF'}.get(x['name'],x['name']):x['bit_length'] for x in binding['files'] }
    bits=[bb[name] for name in obj['constants']]
    bound=max(sum(abs(c) << sum(ei*bi for ei,bi in zip(e,bits)) for e,c in rr.items())
              for poly in ordinary for rr in poly.values())
    # beta_source > 4*(31+2)^2 * max coefficient, even exponent.
    threshold=4*(n+2)**2*bound
    be=threshold.bit_length()
    if be%2:be+=1
    assert (1<<be)>threshold
    return norms,recipes,dict(native_port_bits=bits,ordinary_coefficient_upper_bits=bound.bit_length(),
                             source_beta_exponent=be,bound_multiplier=4*(n+2)**2)


def source(d,v,obj,rs,mode='multi'):
    ww,wcert=weights();ws=ww[1:];t=max(ws);nu=len(ws);r=len(rs)
    norms,recipes,bcert=canonical_residual_coefficients(obj,rs)
    A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const
    b=d.save('b',A(c(1),M(c(3),v['f'])))
    base=d.save('base',M(d.fixed('beta_source'),P(b,2)))
    top=d.save('top',P(base,t))
    vp=[top]+[P(base,t-w) for w in ws]
    @lru_cache(None)
    def horner(ts):
        if not ts:return c(0)
        counts=[sum(ex[j]>0 for ex,co in ts) for j in range(nu+1)]
        if not max(counts):return A(*(co for ex,co in ts))
        j=max(range(nu+1),key=lambda j:(counts[j],sum(ex[j] for ex,co in ts),j))
        yes=[];no=[]
        for ex,co in ts:
            if ex[j]:
                ee=list(ex);ee[j]-=1;yes.append((tuple(ee),co))
            else:no.append((ex,co))
        return A(horner(tuple(no)),M(vp[j],horner(tuple(yes))))
    H=[]
    for j,rec in norms:
        terms=tuple(((2-sum(alpha),)+tuple(alpha),c(name) if isinstance(name,int) else d.fixed(name))
                    for alpha,name in rec)
        H.append(horner(terms))
    step=P(base,2*t+1)
    Dcode=c(0)
    for hj in reversed(H):Dcode=A(hj,M(step,Dcode))
    d.save('Dcode',Dcode)
    ell=d.save('ell',A(*(P(base,w) for w in ws)))
    q_targets=[2*t+j*(2*t+1) for j in range(r)]
    max_target=q_targets[-1];high=max_target+2*t
    _,targetgeo=geometric_pair(d,step,r)
    mask_target=d.save('Qmask',M(P(top,2),targetgeo))
    N0=d.save('N0',M(top,base))
    N1=d.save('N1',M(c(4),P(base,high+1)))
    N=d.save('N',M(N0,N1))
    mask=d.save('Mcode',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    Tcode=d.save('Tcode',A(mask,M(S(base,c(2)),mask_target,N0)))
    _,geosum=geometric_pair(d,base,high+1)
    Jcode=d.save('Jcode',A(M(c(2),P(A(c(1),v['g']),2),Dcode),M(base,geosum)))
    Scode=d.save('Scode',A(v['g'],M(Jcode,N0)))
    Rcode=d.save('Rcode',A(M(A(Scode,Tcode,c(1)),N),Tcode,c(1)))
    X=d.save('X',M(S(N,c(1)),Rcode))
    Y=d.save('Y',P(N,2))
    cap=d.save('Ccap',M(b,top))
    return b,X,Y,cap,recipes,dict(nu=nu,residual_count=r,weights=ws,max_weight=t,
            target_exponents=q_targets,coefficient_degree=max_target,convolution_degree=high,
            N_exponent=t+high+2,source_degree=2,residual_order=[j for j,_ in rs],
            weight_certificate=wcert,coefficient_bound=bcert,
            parent_sha256=hashlib.sha256(PARENT.read_bytes()).hexdigest())


def construct():
    obj,rs=shifted_residuals()
    d=DAG();A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const
    v={name:d.var(name) for name in VARIABLES}
    b,X,Y,cap,recipes,certificate=source(d,v,obj,rs)
    # Downstream inherited Sun bridge, local coprime square merge, quintic
    # merger and structural separating weights; literal adaptation of pkg31.
    L=d.save('Lsmall',M(v['l'],Y));U=d.save('U',M(c(2),L,X))
    V=d.save('V',M(c(4),v['g'],v['w'],Y));W=d.save('Wsmall',M(b,v['w']))
    AA=d.save('A',M(U,A(V,c(1))));BB=d.save('Bsmall',A(M(c(2),X),c(1)))
    C=d.save('C',A(BB,M(S(AA,c(2)),v['h'])))
    Pn=d.save('Pn',M(P(U,2),V));K=d.save('K',A(X,c(1),M(v['k'],S(Pn,c(2)))))
    SS=d.save('Ssmall',S(M(c(2),AA),c(5)))
    TT=d.save('Tsmall',S(M(c(3),W,C),M(c(2),S(P(W,2),c(1)))))
    R2=d.save('R2',A(M(S(P(Pn,2),c(4)),P(K,2)),c(4)))
    cap3=P(cap,3)
    Delta=d.save('Delta',S(M(c(8),cap3,v['g'],P(K,2)),M(P(v['g'],2),A(M(c(32),P(S(C,M(K,L)),2),cap3),M(P(v['g'],2),P(K,2))))))
    O0=d.save('O0',M(P(v['f'],2),P(v['l'],2),Delta))
    xi=d.save('xi',M(v['z'],v['x']))
    D=d.save('D',A(M(S(P(AA,2),c(4)),P(C,2)),c(4)))
    E=d.save('E',M(P(C,2),D,xi))
    F=d.save('F',A(M(c(4),S(P(AA,2),c(4)),P(E,2)),c(1)))
    Gstar=d.save('Gstar',S(M(c(2),A(AA,c(2)),P(S(AA,c(2)),2),P(E,2)),c(1)))
    Omega=d.save('Omega',M(c(16),E))
    Hstar=d.save('Hstar',A(C,M(S(BB,C),F),M(Omega,F,v['y'])))
    Istar=d.save('Istar',A(M(S(P(Gstar,2),c(1)),P(Hstar,2)),c(1)))
    Sigma=d.save('Sigma',M(xi,P(SS,5)))
    rr=d.save('merger_argument',A(TT,M(SS,v['y'])))
    SS2=P(SS,2)
    Theta=d.save('Theta',M(S(S(P(rr,3),M(rr,SS2)),M(SS2,SS)),A(P(rr,2),M(c(23),SS2))))
    positivity=S(M(c(3),O0),c(4))
    bracket=d.save('positivity_bracket',A(c(1),M(positivity,P(b,2),P(v['z'],2))))
    radicands=[M(b,bracket),R2,M(D,F,Istar)]
    for j,value in enumerate(radicands,1):d.save('A'+str(j),value)
    weight1=d.save('norm_weight1',radicands[0])
    weight2=d.save('norm_weight2',M(weight1,A(P(Pn,2),P(K,2),c(3))))
    ws=[c(1),weight1,weight2]
    center=d.save('norm_center',S(M(Sigma,v['m']),Theta));Sigma2=P(Sigma,2)
    scaled=[d.save('scaled_A'+str(j+1),M(Sigma2,P(ws[j],2),value)) for j,value in enumerate(radicands)]
    out=d.save('F10',quadratic_norm(d,center,scaled))
    nodes,output,names=d.prune(out)
    degree=[]
    for node in nodes:
        k=node['kind']
        degree.append(1 if k=='variable' else 0 if k in ('fixed','literal') else
                      degree[node['left']]+degree[node['right']] if k=='mul' else
                      max(degree[node['left']],degree[node['right']]))
    body=dict(schema='proveit-direct-quadratic10-compact-v1',domain='unrestricted integers',
              variables=VARIABLES,nodes=nodes,output=output,named_nodes=names,
              degree_upper_bound=degree[output],
              named_degree_upper_bounds={key:degree[i] for key,i in names.items()},
              operation_counts={kind:sum(n['kind']==kind for n in nodes) for kind in ['add','sub','mul']},
              fixed_binding='data/INSTANCE.json',proof='DIRECT_QUADRATIC_PROOF.md',
              coefficient_ports=obj['constants'],coefficient_recipes=recipes,
              source_certificate=certificate,
              attribution='Source encoding new in this package; Sun 2021/2026 bridge and package31 finalizer.')
    return body


def main():
    if not __debug__:raise RuntimeError('Run without -O: assertion checks must remain enabled.')
    body=construct();out=UP/'generated';out.mkdir(exist_ok=True)
    (out/'direct10_compact.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
    (out/'source_certificate.json').write_text(json.dumps(body['source_certificate'],indent=2)+'\n')
    print(json.dumps({'degree_upper_bound':body['degree_upper_bound'],
          'ops':body['operation_counts'],'operations':sum(body['operation_counts'].values()),
          'fixed_leaves':sum(n['kind']=='fixed' for n in body['nodes']),
          'source':body['source_certificate']},indent=2))
if __name__=='__main__':main()
