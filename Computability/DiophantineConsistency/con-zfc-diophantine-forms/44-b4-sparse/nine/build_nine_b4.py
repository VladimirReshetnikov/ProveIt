#!/usr/bin/env python3
"""Fixed-polynomial B4 Jones front end and sharp nine-variable finalizer.
All fixed powers are division-free binary circuits. No implicit witnesses.
"""
from pathlib import Path
import json
from circuit import DAG, canonical_keys
from b4_support import coding_blocks_b4, geometric_pair, quadratic_norm
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'sun/sources/data'
WEIGHTS=ROOT.parent/'root_checks/bose_chowla_31_optimized.json'
NATURAL_VARIABLES=['epsilon','g0','h0','s0','w0','phi','i0','j0','n']
POSITIVE_VARIABLES=['epsilon_plus','g','h','s','w','phi_plus','i','j','n_plus']
INDEX_EXPONENT=4269855
KAPPA=4269877

def construct(positive=False, certificate=False):
    VARIABLES=POSITIVE_VARIABLES if positive else NATURAL_VARIABLES
    constants=json.loads((SOURCE/'constants.json').read_text())
    ws=json.loads(WEIGHTS.read_text())['weights_with_zero'][1:]
    t=max(ws)
    keys,aliases=canonical_keys(constants)
    d=DAG(); A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const
    vv={name:d.var(name) for name in VARIABLES}
    if positive:
        v={name:vv[name] for name in ['g','h','s','w','i','j']}
        v.update({name:S(vv[name+'_plus'],c(1)) for name in ['epsilon','phi','n']})
    else:
        v={name:A(vv[name+'0'],c(1)) for name in ['g','h','s','w','i','j']}
        v.update({name:vv[name] for name in ['epsilon','phi','n']})
    save=d.save
    b=save('b',A(c(1),vv['epsilon_plus']) if positive else A(c(2),v['epsilon']))
    base=save('base',M(d.fixed('base_scale'),P(b,4)))
    qcode,ell,Dcode,top=coding_blocks_b4(d,base,keys,ws)
    for name,val in [('qcode',qcode),('ell',ell),('Dcode',Dcode),('top',top)]:save(name,val)
    N0=save('N0',M(top,base))
    N1=save('N1',M(c(2),P(top,8),base))
    N=save('N',M(N0,N1))
    mask=save('Mcode',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    Tcode=save('Tcode',A(mask,M(S(base,c(2)),qcode,N0)))
    _,geo=geometric_pair(d,base,8*t+1)
    Jcode=save('Jcode',A(M(c(2),P(A(c(1),v['g']),4),Dcode),M(base,geo)))
    Scode=save('Scode',A(v['g'],M(Jcode,N0)))
    R=save('R',M(S(N,c(1)),A(M(A(Scode,Tcode,c(1)),N),Tcode,c(1))))
    Gcap=save('Gcap',M(c(32),b,top))
    omega=save('omega',v['w']);N2=P(N,2)
    U=save('U',M(N2,omega)); Y=save('Y',M(N2,v['s'])); MM=save('M',M(R,Y))
    PellP=save('P',M(c(2),P(MM,2),U));K=save('K',A(R,c(1),M(v['h'],S(PellP,c(1)))))
    AA=save('A',M(MM,A(U,c(1))));B1=save('B1',A(M(c(2),R),c(1)))
    W1=save('W1',M(b,omega));C=save('C',A(M(c(2),R),W1,vv['phi_plus']) if positive else A(B1,W1,v['phi']));J=save('J',S(M(c(4),AA),c(5)))
    Q=save('Q',S(M(c(3),W1,C),M(c(2),S(P(W1,2),c(1)))))
    Aminus=S(P(AA,2),c(1));C2=P(C,2)
    D=save('D',A(M(Aminus,C2),c(1)));E=save('E',M(v['i'],J,D,C2))
    F=save('F',A(M(Aminus,P(E,2)),c(1)))
    GG=save('G',A(AA,M(F,S(A(M(C,D),c(1)),AA))))
    H=save('H',A(B1,M(v['j'],C)));I=save('I',A(M(S(P(GG,2),c(1)),P(H,2)),c(1)))
    a0=save('a0',A(S(P(M(PellP,K),2),P(K,2)),c(1)))
    a1=save('a1',M(c(64),D,F,I))
    margin=save('margin',S(M(P(K,2),Gcap),A(M(c(4),P(S(C,M(K,Y)),2),Gcap),M(c(8),v['g'],P(K,2)))))
    u=save('u',M(J,F));vdiv=save('v',A(M(Q,F),M(J,S(H,C))))
    V0=save('V0',M(PellP,K))
    norm_t=save('norm_t',M(v['i'],J,C))
    approx=save('approx',M(norm_t,S(S(M(c(8),P(D,2)),M(c(4),D)),c(1))))
    GH=save('GH',M(GG,H)); rootcap=save('rootcap',M(approx,GH))
    V1=save('V1',rootcap)
    Mdiv=save('Mdiv',A(Q,S(H,C)))
    Omega=save('Omega',M(u,S(M(c(2),margin),c(1))))
    E0=save('E0',S(A(M(u,v['n']),vdiv),M(Omega,Mdiv)))
    Theta=save('Theta',S(E0,M(Omega,V0,V1)))
    if not certificate:
        inner=save('inner',S(P(Theta,2),M(P(Omega,2),A(a0,M(P(V0,2),a1)))))
    else:
        dferror=save('dferror',S(M(P(norm_t,2),A(M(c(8),D),c(1))),M(c(64),D)))
        deltaV=save('deltaV',A(M(dferror,P(GH,2)),M(c(64),D,F,S(P(H,2),c(1)))))
        inner=save('inner',S(A(S(P(E0,2),M(c(2),E0,Omega,V0,V1)),M(P(Omega,2),P(V0,2),deltaV)),M(P(Omega,2),a0)))
    out=save('nine_b4',S(P(inner,2),M(c(4),P(Omega,4),P(V0,2),a0,a1)))
    nodes,output,names=d.prune(out)
    body={'schema':'proveit-jones-b4-nine-v1','domain':'positive integers' if positive else 'nonnegative integers',
      'variables':VARIABLES,'t':t,'L':4*t,'m':8*t+1,'Ecode':9*t+2,'witness_weights':ws,
      'nodes':nodes,'output':output,'named_nodes':names,
      'operation_counts':{k:sum(x['kind']==k for x in nodes) for k in ('add','sub','mul')},
      'fixed_binding':'../../sun/sources/data/coefficients_binding.json',
      'fixed_recipes':{'source_coefficients':'../../sun/sources/data/constants.json','base_scale':f'2^{KAPPA}'},
      'proof':'../NINE_B4_PROOF.md', 'degree_certificate_variant':certificate}
    assert [n['name'] for n in nodes if n['kind']=='variable']==VARIABLES
    return body,aliases


def degree_certificate(body):
    """Exact diagonal leaders as sparse polynomials in fixed base_scale.

    Unknown coefficient-dependent heads remain None. A monomial final head
    is nonzero since base_scale is a specified positive power of two.
    """
    rows=[];unresolved=[]
    for idx,n in enumerate(body['nodes']):
        if n['kind']=='variable':row=(1,{0:1})
        elif n['kind']=='literal':row=(0,{0:n['value']})
        elif n['kind']=='fixed':row=(0,{1:1} if n['name']=='base_scale' else None)
        else:
            da,ca=rows[n['left']];db,cb=rows[n['right']]
            if n['kind']=='mul':
                if ca is None or cb is None:row=(da+db,None)
                else:
                    cc={}
                    for ea,aa in ca.items():
                        for eb,bb in cb.items():cc[ea+eb]=cc.get(ea+eb,0)+aa*bb
                    row=(da+db,{k:v for k,v in cc.items() if v})
            else:
                sg=1 if n['kind']=='add' else -1
                if da>db:row=(da,ca)
                elif db>da:row=(db,None if cb is None else {k:sg*v for k,v in cb.items()})
                elif ca is None or cb is None:row=(da,None)
                else:
                    cc=ca.copy()
                    for k,v in cb.items():cc[k]=cc.get(k,0)+sg*v
                    cc={k:v for k,v in cc.items() if v}
                    if not cc and da>0:unresolved.append(idx)
                    row=(da,cc)
        rows.append(row)
    degree,head=rows[body['output']]
    assert head is not None and len(head)==1 and next(iter(head.values()))!=0
    assert not unresolved,unresolved
    bp,scalar=next(iter(head.items()))
    return {'exact_degree':degree,'diagonal_leading_coefficient':{'scalar':scalar,'base_scale_power':bp},
      'fixed_leaf_heads':'Unknown except base_scale; final monomial head is explicitly positive',
      'named_degrees':{name:rows[idx][0] for name,idx in body['named_nodes'].items()},
      'named_leaders':{name:rows[idx][1] for name,idx in body['named_nodes'].items()},
      'unresolved_positive_degree_cancellations':unresolved}


def main():
    out=ROOT/'generated';out.mkdir(exist_ok=True)
    bodies={}
    for positive in [False,True]:
        label='positive' if positive else 'natural'
        body,aliases=construct(positive)
        certbody,_=construct(positive,True)
        cert=degree_certificate(certbody)
        body['exact_degree']=cert['exact_degree'];certbody['exact_degree']=cert['exact_degree']
        (out/f'nine_b4_{label}.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
        (out/f'nine_b4_{label}_certificate.json').write_text(json.dumps(certbody,separators=(',',':'))+'\n')
        (out/f'{label}_DEGREE_CERTIFICATE.json').write_text(json.dumps(cert,indent=2)+'\n')
        bodies[label]={'degree':cert['exact_degree'],'operations':body['operation_counts'],'total':sum(body['operation_counts'].values())}
    (out/'coefficient_aliases.json').write_text(json.dumps(aliases,indent=2)+'\n')
    print(json.dumps(bodies,indent=2))
if __name__=='__main__':main()
