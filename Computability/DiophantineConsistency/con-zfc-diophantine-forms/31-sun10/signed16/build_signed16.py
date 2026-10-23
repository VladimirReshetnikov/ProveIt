#!/usr/bin/env python3
"""Build the fully specified sixteen-integer equation of this report.

No consistency/halting search, floating point, symbolic exponent, division,
radical, or hidden witness is used in the output polynomial.
"""
from pathlib import Path
import json
from circuit import DAG,coding_blocks,canonical_keys

ROOT=Path(__file__).resolve().parent
GUARDS=['g0','s0','w0','phi','j0']

def construct():
    constants=json.loads((ROOT/'data/constants.json').read_text())
    nu=constants['nu']; L=5**(nu+1)
    keys,aliases=canonical_keys(constants)
    d=DAG(); A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const
    v={s:d.var(s) for s in ['t','g0','h0','s0','w0','phi','i0','j0']}
    z=d.fixed('z_index'); kap=d.fixed('kappa_index')
    b=d.save('b',M(kap,P(v['t'],2)))
    g,h,s,w,ii,jj=[A(v[n],c(1)) for n in ['g0','h0','s0','w0','i0','j0']]
    B=d.save('B',P(b,5))
    q,ell,lam,e,top=coding_blocks(d,B,nu,keys,z)
    for name,n in [('q',q),('ell',ell),('lambda',lam),('e',e)]:d.save(name,n)
    theta=S(B,M(c(2),z)); N=d.save('N',P(q,16)); Gcap=d.save('Gcap',M(c(32),b,top))
    Rleft=A(g,M(e,P(q,3)),M(ell,P(q,5)),
            M(A(M(c(2),S(e,M(z,lam)),P(A(c(1),B,g),4)),
                M(lam,B),M(lam,B,P(q,4))),P(q,7)))
    Rright=A(S(P(q,3),M(b,ell)),ell,M(theta,lam,P(q,3)),M(S(B,c(2)),P(q,8)))
    R=d.save('R',A(M(Rleft,S(P(N,2),N)),M(Rright,S(P(N,2),c(1)))))
    U=d.save('U',M(P(N,2),w)); Y=d.save('Y',M(P(N,2),s))
    MM=d.save('M',M(R,Y)); PP=d.save('P',M(c(2),P(MM,2),U))
    K=d.save('K',A(R,c(1),M(h,S(PP,c(1)))))
    AA=d.save('A',M(MM,A(U,c(1))))
    Bprime=A(M(c(2),R),c(1)); W=d.save('Wsmall',M(b,w))
    C=d.save('C',A(Bprime,W,v['phi'])); J=d.save('J',S(M(c(4),AA),c(5)))
    Q=d.save('Q',S(M(c(3),W,C),M(c(2),S(P(W,2),c(1)))))
    D=d.save('D',A(M(S(P(AA,2),c(1)),P(C,2)),c(1)))
    E=d.save('E',M(ii,J,D,P(C,2)))
    F=d.save('F',A(M(S(P(AA,2),c(1)),P(E,2)),c(1)))
    Gp=d.save('Gp',A(AA,M(F,S(A(M(C,D),c(1)),AA))))
    H=d.save('H',A(Bprime,M(jj,C)))
    I=d.save('I',A(M(S(P(Gp,2),c(1)),P(H,2)),c(1)))
    a0=d.save('a0',A(M(S(P(PP,2),c(1)),P(K,2)),c(1)))
    a1=d.save('a1',M(D,F,I))
    margin=d.save('margin',S(S(M(P(K,2),Gcap),M(c(4),P(S(C,M(K,Y)),2),Gcap)),M(c(8),g,P(K,2))))
    zz=[d.var('z'+str(j)) for j in range(1,7)]
    stack=c(1)
    for j,name in enumerate(GUARDS):
        disc=A(M(c(3),v[name]),c(2))
        factor=A(c(1),M(c(4),disc,P(stack,2),P(zz[j],2)))
        stack=d.save('guard'+str(j+1),M(stack,factor))
    disc=S(M(c(3),margin),c(1))
    stack=d.save('guard6',M(stack,A(c(1),M(c(4),disc,P(stack,2),P(zz[5],2)))))
    DD=d.save('Ddiv',M(J,F)); TT=d.save('Tdiv',A(M(Q,F),M(J,S(H,C))))
    nz=d.save('Znonzero',M(ii,*zz))
    denom=d.save('Smerge',M(nz,P(DD,5)))
    residue=d.var('v'); normroot=d.var('u')
    r=A(TT,M(DD,residue)); DD2=P(DD,2)
    homogeneous=d.save('Tmerge',M(S(S(P(r,3),M(DD2,r)),M(DD2,DD)),A(P(r,2),M(c(23),DD2))))
    weight1=d.save('weight1',stack)
    V0=d.save('V0',A(P(PP,2),P(K,2),c(2)))
    weight2=d.save('weight2',M(stack,V0))
    X=d.save('Xnorm',S(M(denom,normroot),homogeneous)); S2=P(denom,2)
    A0=d.save('A0norm',M(S2,stack))
    common=M(S2,P(stack,2))
    A1=d.save('A1norm',M(common,a0))
    A2=d.save('A2norm',M(common,P(V0,2),a1))
    X2=P(X,2)
    V=d.save('Vnorm',S(S(A(X2,A2),A0),A1)); V2=P(V,2)
    fourXB=M(c(4),X2,A2)
    Wn=d.save('Wnorm',S(A(V2,fourXB),M(c(4),A0,A1)))
    out=d.save('F16',S(P(Wn,2),M(c(4),V2,fourXB)))
    nodes,output,names=d.prune(out)
    variables=[n['name'] for n in nodes if n['kind']=='variable']
    assert len(variables)==16 and len(set(variables))==16
    assert 'epsilon' not in variables and 'n' not in variables
    body={'schema':'proveit-signed16-v1','domain':'unrestricted integers','variables':variables,
          'nu':nu,'L':L,'nodes':nodes,'output':output,'named_nodes':names,
          'operation_counts':{k:sum(n['kind']==k for n in nodes) for k in ['add','sub','mul']},
          'exact_degree':813056*L+10016,'exact_degree_formula':'813056*5^32+10016',
          'fixed_binding':'data/INSTANCE.json','proof':'../report.tex, signed16 sections',
          'counting':'Each binary +,-,* is one operation; fixed leaves and reuse free; fixed powers expanded.'}
    return body,aliases

def main():
    body,aliases=construct(); out=ROOT/'generated';out.mkdir(exist_ok=True)
    (out/'signed16.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
    (out/'coefficient_aliases.json').write_text(json.dumps(aliases,indent=2)+'\n')
    print(json.dumps({'variables':len(body['variables']),'degree':body['exact_degree'],
                      'operations':body['operation_counts'],'total':sum(body['operation_counts'].values()),
                      'fixed_leaves':sum(n['kind']=='fixed' for n in body['nodes'])},indent=2))
if __name__=='__main__':main()
