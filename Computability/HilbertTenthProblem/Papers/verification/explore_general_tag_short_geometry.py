"""All deletion numbers: scoped first-step halting under R>=K^2 H.

The fixed C is enlarged freely. The numerical range is a theorem hypothesis,
not an added free operation or a proof of unrestricted104 soundness.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import sympy as sp

import explore_tag_radix_divisibility_omission as omission
import explore_general_scaled_tag_transport as generic
import explore_nonpower_tag_first_symbol as first


def constants(beta, app):
    c = generic.tag.constants(beta, app)
    while c['C'] <= c['K']**2:
        c['C'] *= 3
    return generic.extended(c)


def symbolic():
    R,H,q,L,Li,Lf,M1,B,k=sp.symbols('R H q L Li Lf M1 B k')
    O=L+(B-1)*M1
    geom=H*(R-1)-q+1
    length=R*O-k*(L-Li+q*Lf)
    collapse=R*(O-k*Lf*H)-k*(L-Li-Lf*(H-1))
    assert sp.expand(collapse-length+k*Lf*geom)==0
    marker=(B-1)*M1-((k-1)*Lf*H+Lf-Li)
    assert sp.expand(marker-(O-k*Lf*H)+(L-Li-Lf*(H-1)))==0
    assert sp.expand(((k-1)*Lf*H+Lf-Li).subs(Li,k*Lf)-(k-1)*Lf*(H-1))==0
    records=[omission.verify_source(e) for e in (0,1)]
    return dict(exact_identities=3,
                unchanged_sources=[{n:r[n] for n in ('leading','operations','multiplications',
                                                    'additions','positive_unknowns','equations')}
                                   for r in records],
                scope='Fixed C changes numerals only; no short-geometry comparison is added or counted.')


def rational_bounds():
    count=boundary=0
    for beta in range(1,7):
        K=3**beta; k=K//3; C=3*K*K
        for H in (1,2,3,10,100,1000):
            for R in (max(K**3+1,K*K*H),max(K**3+1,2*K*K*H),max(K**3+1,10*K*K*H)):
                q=(R-1)*H+1
                assert R>K**3 and R>=K*K*H and q<=R*H
                assert R>k*(k*K+1)
                Lbound=Fraction(k*K*q,R-k)
                assert Lbound<(k*K+1)*H
                upper=Fraction((k*K+1)*H,R)
                lower=-Fraction(1,C)-Fraction(K*H,R)
                assert -1<lower<0<upper<1
                assert Fraction(k*K+1,K*K)==Fraction(1,3)+Fraction(1,K*K)
                count+=1;boundary+=R==K*K*H
    return dict(exact_rational_cases=count,exact_R_eq_K2H=boundary)


def marker_channels():
    trials=accepted=zero=one=lead_two=0
    # These local tuples assume the derived collapse and least-marker facts.
    # They need not have a complete q or satisfy the original transport.
    for beta in range(1,5):
        K=3**beta; k=K//3; m=2*beta+2; h=3**m
        for lead in (0,1,2,4,5,7,8,10,11):
            H=1+h*lead
            for Lf in range(1,K):
                for ell in range(beta,2*beta+2):
                    Li=3**ell; L=Li+Lf*(H-1); O=k*Lf*H
                    if first.v3(L)!=ell or (L//Li)%3!=1:
                        continue
                    for a in range(2,6):
                        trials+=1; B=3**(a-1)
                        if (O-L)%(B-1):
                            continue
                        M1=(O-L)//(B-1); M0=L-M1
                        if not generic.tag.boolean(M0) or not generic.tag.boolean(M1):
                            continue
                        assert ell<=beta-1+first.v3(Lf)<=2*beta-2<m
                        assert L%h==Li and k*Lf<h
                        assert Lf==3**first.v3(Lf)
                        if M1%h==0:
                            assert M0%h==Li and k*Lf==Li
                            assert (B-1)*M1==(k-1)*Lf*(H-1)
                            if H>1:
                                assert beta>=2 and M1>0
                                assert first.v3(M1)==m+first.v3(Lf)
                                assert (M1//3**first.v3(M1))%3==lead%3==1
                            zero+=1
                        else:
                            assert M0%h==0 and M1%h==Li and k*Lf==B*Li<h
                            one+=1
                        accepted+=1
        # Leading2 is independently tested on exact positive zero-channel
        # quotients, before applying the Boolean mask.
        if beta>=2:
            for s in range(1,beta):
                for lead in (2,5,8,11):
                    H=1+h*lead; Lf=3**s
                    for a in range(2,6):
                        B=3**(a-1); num=(k-1)*Lf*(H-1)
                        if num%(B-1):
                            continue
                        M1=num//(B-1)
                        assert first.v3(M1)==m+s
                        assert (M1//3**(m+s))%3==2 and not generic.tag.boolean(M1)
                        lead_two+=1
    assert accepted and zero and one and lead_two
    return dict(marker_trials=trials,accepted_structural_tuples=accepted,
                low_M0_cases=zero,low_M1_cases=one,leading_two_rejections=lead_two,
                scope='Collapsed length/marker tuples only. Both H leading units occur in the tested range; full geometry and content are not asserted for these structural cases.')


def local_guard():
    words=reject=0
    for m in range(4,10):
        h=3**m
        for bits in product((0,1),repeat=m):
            Q=sum(b*3**i for i,b in enumerate(bits)); words+=1
            if (2*Q+1)%h:
                continue
            assert Q==(h-1)//2
            for j in range(1,m):
                for tail in (0,1,2,5):
                    A=3**j*(1+3*tail)
                    G=(Q+A)%h
                    assert (G//3**j)%3==2 and not generic.tag.boolean(G)
                    reject+=1
    return dict(low_Q_words=words,forced_guard_rejections=reject)


def one_step_witness(beta, app, initial, padding):
    c=constants(beta,app); K=c['K']; Li=3**len(initial)
    Ni=generic.tag.value(initial); sel=initial[0]
    final=initial[beta:]+(app if sel else (0,))
    assert len(initial)>=beta and len(final)<beta
    A=Li*3**padding; R=c['C']*A; q=R; H=1
    ns=(Li-1)//2; d=Ni%K; e=(d-sel)//3; Q=sel*ns
    raw=dict(Gstar=Q+A+1-sel,Q=Q,S0=1-sel,S1=sel,
             M0=(1-sel)*Li,M1=sel*Li,Ebar=c['c']-e,E=e,Nbar=ns-Ni,N=Ni)
    T=(Ni-sel)//3 if c['leading']==0 else (Ni+2*Q)//3
    Nf=generic.tag.value(final); Lf=3**len(final)
    s=dict(F_Q=Q+1,F_S1=sel+1,F_T=T+1,F_E=e+1,F_Nfinal=Nf+1,
           Nsum=ns,A=A,R=R,q=q,H=H,L=Li,Lfinal=Lf,Ninit=Ni,Linit=Li,
           alphaI=A-Li,alphaH=K-Lf)
    before=generic.old.run(omission.prefix(c)[0][:-3],s)
    P=before[omission.prefix(c)[1]]; D0=q**10; r=P+(D0-1)//2
    s.update(r=r,betaP=D0-r)
    out=generic.old.run(omission.prefix(c)[0],s)
    out.update(K=K,pell_tr1=2*r+1)
    assert all(out[a]==out[b] for a,b in omission.outer_comparisons())
    assert all(v>0 for n,v in s.items() if n not in generic.PARAMETERS)
    assert all(0<=v<q and generic.tag.boolean(v) for v in raw.values())
    assert P==sum(raw[f]*q**j for j,f in enumerate(generic.FIELDS))
    assert c['C']>K*K and R>=K*K*H
    assert D0>=81 and 27<=r<D0 and D0<r*r
    exponent=10*first.v3(q)
    assert generic.old.unit.mask_expected(r,exponent) and generic.old.unit.valuation(r)==exponent
    z=dict(raw,q=q,R=R,H=H,A=A,Ninit=Ni,Linit=Li,Nfinal=Nf,Lfinal=Lf,L=Li)
    assert first.check(c,z)['first_symbol']==sel
    k=c['Khalf']; O=raw['M0']+c['B']*raw['M1']
    assert O==k*Lf*H and Li==Li+Lf*(H-1)
    return sel,c['leading'],r%2


def witnesses():
    cases=programs=words=0; selected=[0,0];branches=[0,0];parities=[0,0]
    for beta in (2,3,4):
        for a in (2,3,4):
            for app in product((0,1),repeat=a):
                programs+=1
                for length in range(beta,2*beta-1):
                    for initial in product((0,1),repeat=length):
                        final=initial[beta:]+(app if initial[0] else (0,))
                        if len(final)>=beta:
                            continue
                        words+=1
                        for padding in (1,2):
                            sel,branch,parity=one_step_witness(beta,app,initial,padding)
                            cases+=1;selected[sel]+=1;branches[branch]+=1;parities[parity]+=1
    assert min(selected)>0 and min(branches)>0
    return dict(fixed_programs=programs,one_step_inputs=words,complete_outer_tuples=cases,
                selector_cases=selected,leading_branch_cases=branches,index_parities=parities,
                outer_comparisons_per_tuple=9,masked_words_per_tuple=10,
                scope='All actual first-step halts within the stated finite input/program ranges, at two widened power radices. All outer sources, masks and index valuations are fresh; general44 supplies the huge positive Pell auxiliaries.')


def widened_nonpower_witnesses():
    records=[]
    for k in (8,9,12,16):
        f=omission.family(k)
        c=constants(3,(0,1,0))
        assert c['C']==2187 and c['C']>c['K']**2
        R,q,H=f['R'],f['q'],f['H']; A=R//c['C']
        assert R%c['C']==0 and A>81
        raw=dict(f['raw_fields'])
        raw['Gstar']=raw['Q']+A*H+raw['S0']
        assert A*H==3**(4*k-7)+3**(k-7)
        s=dict(F_Q=raw['Q']+1,F_S1=raw['S1']+1,F_T=f['T']+1,
               F_E=raw['E']+1,F_Nfinal=2,Nsum=f['content_sum'],
               A=A,R=R,q=q,H=H,L=f['length_sum'],Lfinal=9,
               Ninit=27,Linit=81,alphaI=A-81,alphaH=18)
        before=generic.old.run(omission.prefix(c)[0][:-3],s)
        P=before[omission.prefix(c)[1]]; D0=q**10; r=P+(D0-1)//2
        s.update(r=r,betaP=D0-r)
        out=generic.old.run(omission.prefix(c)[0],s)
        out.update(K=c['K'],pell_tr1=2*r+1)
        assert all(out[a]==out[b] for a,b in omission.outer_comparisons())
        assert all(v>0 for name,v in s.items() if name not in generic.PARAMETERS)
        assert P==sum(raw[name]*q**j for j,name in enumerate(generic.FIELDS))
        assert all(0<=v<q and generic.tag.boolean(v) for v in raw.values())
        assert R>=c['K']**2*H and q%R!=0 and R!=3**first.v3(R)
        assert D0>=81 and 27<=r<D0 and D0<r*r
        assert generic.old.unit.mask_expected(r,40*k)
        assert generic.old.unit.valuation(r)==40*k
        oldP=sum(f['raw_fields'][name]*q**j for j,name in enumerate(generic.FIELDS))
        assert P!=oldP
        z=dict(raw,q=q,R=R,H=H,A=A,Ninit=27,Linit=81,Nfinal=1,Lfinal=9,L=f['length_sum'])
        assert first.check(c,z)['first_symbol']==0
        assert z['L']==81+9*(H-1)
        assert z['M0']+c['B']*z['M1']==c['Khalf']*9*H
        records.append(dict(k=k,C=c['C'],A=A,R=R,q=q,H=H,valuation=40*k,
                            outer_equations=9,masked_words=10,old_index_changed=True,
                            first_step_halts=True,full_positive_kernel_hypotheses=True))
    return dict(complete_nonpower_tuples=len(records),cases=records,
                scope='The existing true-halting nonpower family is rechecked at enlarged C2187 with changed A,Gstar,P,r and input slack. All nine outer equations and ten masks are actual; fresh generic44 witnesses exist at the changed index. R does not divide q, so no implicit radix recovery is claimed.')


def verify():
    return dict(status='PASS_GENERAL_TAG_SHORT_GEOMETRY',sources=symbolic(),
                bounds=rational_bounds(),markers=marker_channels(),guard=local_guard(),
                witnesses=witnesses(),widened_nonpower=widened_nonpower_witnesses(),
                proof='../1980/EXPLORATION_GENERAL_TAG_SHORT_GEOMETRY.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; the added enlarged-constant nonpower family also passed both independent focused reviews and fresh runs. Proof and arithmetic frozen.',
                scope='With fixed C>K^2 and the external range R>=K^2H, the unchanged weakened104 source is equivalent to halting after the first actual step. No R-power or H-Boolean premise is used for soundness. No unrestricted104 bound or free range comparison is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print({k:v for k,v in result.items() if k not in ('sources','proof','scope','review')})
