"""Forced opposite index parities in unchanged105, including formal suffixes."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_general_scaled_tag_transport as base


def parity(length):
    return sum(j+1 for j in range(2,length+1))%2


def boolean_words(digits):
    return [sum(b*3**i for i,b in enumerate(bits))
            for bits in product((0,1),repeat=digits)]


def symbolic():
    Q,H,A,S1,L,Ns,c=sp.symbols('Q H A S1 L Ns c')
    # Pair sums make this identity independent of the individual complements.
    total=Q+A*H+H-S1+Q+H+L+c*H+Ns
    assert sp.expand(total-(c*H+Ns-S1)-2*(Q+2*H+Ns)-
                     (A-1)*H-(L-2*Ns-H))==0
    source=base.verify_source_branch(0)
    return dict(operations=source['operations'],multiplications=source['multiplications'],
                additions=source['additions'],positive_unknowns=source['positive_unknowns'],
                equations=source['equations'],source_comparisons=len(source['sources']),
                total_field_sum=sp.sstr(total),
                parity_identity='P = cH+Nsum-S1 modulo2, using odd A and L=2Nsum+H')


def content_gate():
    tested=accepted=0
    for m,t in ((3,1),(3,2),(3,3),(4,1),(4,2),(4,3)):
        R=3**m;q=R**t;shift=R//9;H=(q-1)//(R-1)
        prefix_support=4*H  # Unit and next trit of every row.
        for N in boolean_words(m*t):
            for Nt in range(9):
                tested+=1
                numerator=(shift-1)*N-q*Nt
                if numerator<0 or numerator%shift:continue
                d=numerator//shift
                if not base.tag.boolean(d):continue
                if any(a and not b for a,b in zip(base.tag.trits(d),
                                                base.tag.trits(prefix_support))):continue
                if d>prefix_support:continue
                assert shift*N==N+shift*d+q*Nt
                assert shift*d<q
                assert N==d==Nt==0
                accepted+=1
    return dict(candidates=tested,accepted=accepted,
                scope='Complete Boolean N words and Nfinal=0..8 at six small geometries; d is solved exactly and tested for the paid two-trit prefix support. No claim these small widths meet the complete105 fixed-C input bound.')


def row_gate():
    tested=nonempty=empty=0
    for m in range(1,9):
        R=3**m
        for Nb in boolean_words(m):
            tested+=1
            carry,marker=divmod(2*Nb+1,R)
            if not base.tag.boolean(marker):continue
            if marker:
                assert carry==0 and len([d for d in base.tag.trits(marker) if d])==1
                nonempty+=1
            else:
                assert carry==1 and Nb==(R-1)//2
                empty+=1
    return dict(candidates=tested,nonempty_single_markers=nonempty,empty_outgoing_carries=empty)


def length_gate():
    tested=accepted=0
    for m in range(6,13):
        R=3**m;shift=R//3
        for ell in range(2,m-3):
            for t in range(1,2*ell+5):
                q=R**t;H=(q-1)//(R-1)
                for Lf in range(1,9):
                    tested+=1
                    numerator=q*Lf-3**ell
                    if numerator<=0 or numerator%(shift-1):continue
                    M0=numerator//(shift-1)
                    if not (0<M0<q and base.tag.boolean(M0)):continue
                    if M0<H or (M0-H)%2:continue
                    Nb=(M0-H)//2
                    if not base.tag.boolean(Nb):continue
                    assert (t,Lf) in ((ell-1,3),(ell,1))
                    assert M0==sum(3**(ell-j)*R**j for j in range(t))
                    assert (t+Nb)%2==parity(ell)
                    accepted+=1
    return dict(candidates=tested,accepted=accepted,
                scope='All integer terminal lengths1..8, including nonmarkers, in the stated m/ell/t ranges. The unique length word and complement are solved, not assumed rowwise.')


def full_outer():
    c=base.extended(base.tag.constants(2,(0,0)))
    cases=rows=extensions=0;parities=[0,0]
    examples=[]
    for ell in range(2,13):
        for padding in (1,2,3):
            A=3**(ell+padding);R=c['C']*A
            for extra in (0,1):
                t=ell-1+extra;q=R**t;H=(q-1)//(R-1)
                L=sum(3**(ell-j)*R**j for j in range(t));Ns=(L-H)//2
                s=dict(F_Q=1,F_S1=1,F_T=1,F_E=1,F_Nfinal=1,Nsum=Ns,
                       A=A,R=R,q=q,H=H,L=L,Lfinal=3**(ell-t),
                       Ninit=0,Linit=3**ell,alphaI=A-3**ell,
                       alphaH=9-3**(ell-t),v=q//R)
                before=base.old.run(base.prefix(c)[0][:-3],s)
                P=before[base.prefix(c)[1]];scale=q**10;r=P+(scale-1)//2
                s.update(r=r,betaP=scale-r)
                out=base.old.run(base.prefix(c)[0],s);out.update(K=9,pell_tr1=2*r+1)
                assert all(v>0 for k,v in s.items() if k not in base.PARAMETERS)
                assert all(out[a]==out[b] for a,b in base.outer_comparisons())
                assert all(z==0 for z in base.sources(c,s))
                fields=dict(Gstar=(A+1)*H,Q=0,S0=H,S1=0,M0=L,M1=0,
                            Ebar=H,E=0,Nbar=Ns,N=0)
                assert all(0<=z<q and base.tag.boolean(z) for z in fields.values())
                assert P==sum(fields[f]*q**i for i,f in enumerate(base.FIELDS))
                exponent=10*t*(ell+padding+3)
                assert scale==3**exponent and base.old.unit.valuation(r)==exponent
                assert base.old.unit.mask_expected(r,exponent)
                assert 81<=scale and 27<=r<scale and scale<r*r
                assert r%2==P%2==parity(ell)
                cases+=1;rows+=t;extensions+=extra;parities[r%2]+=1
                if ell in (2,4) and padding==1:
                    examples.append(dict(input_length=ell,Ninit=0,Linit=3**ell,
                                         rows=t,terminal_length=ell-t,width=ell+padding+3,
                                         r_parity=r%2,valuation=exponent))
    assert min(parities)>0
    return dict(full_outer_tuples=cases,rows=rows,formal_posthalt_extensions=extensions,
                even_odd_indices=parities,outer_sources_per_tuple=10,mask_fields_per_tuple=10,
                examples=examples,
                scope='Complete actual105 outer sources, positive supplied outer coordinates, ten masks, index valuation and all generic44 prerequisites. Full positive Pell extension follows the reviewed theorem; enormous auxiliary values are not materialized.')


def verify():
    return dict(status='PASS_TAG_INDEX_PARITY_OBSTRUCTION',source=symbolic(),
                content=content_gate(),row_decoder=row_gate(),length=length_gate(),
                witnesses=full_outer(),proof='../1980/EXPLORATION_TAG_INDEX_PARITY_OBSTRUCTION.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; proof and arithmetic frozen.',
                scope='Unchanged generic105 witnesses cannot all be arranged to one index parity, even for beta2,u00. This does not prove wrong-sign43 unsatisfiability or obstruct a specially compiled universal appendant.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:v for k,v in result.items() if k not in ('source','review','scope','proof')})
