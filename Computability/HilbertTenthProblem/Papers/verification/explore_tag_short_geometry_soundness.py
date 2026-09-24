"""Scoped beta2 soundness when R>=28H, for every appendant length>=2."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_tag_radix_divisibility_omission as omission
import explore_general_scaled_tag_transport as generic
import explore_nonpower_tag_first_symbol as first


def symbolic():
    R,H,q,L,Li,M1,B=sp.symbols('R H q L Li M1 B')
    O=L+(B-1)*M1
    marker=(B-1)*M1-(6*H+3-Li)
    assert sp.expand(marker-(O-9*H)+(L-Li-3*(H-1)))==0
    assert sp.expand((R-1)*(H-1)-(q-R)-(H*(R-1)-q+1))==0
    checks=[omission.verify_source(e) for e in (0,1)]
    return dict(exact_symbolic_identities=2,
                unchanged_sources=[{k:s[k] for k in ('leading','operations','multiplications',
                                                    'additions','positive_unknowns','equations')}
                                   for s in checks],
                scope='Both unchanged104 source schedules are rechecked; no R>=28H comparison is added or counted.')


def least_marker_gate():
    tested=accepted=long_obstructions=0
    for m in range(3,9):
        for lead in range(1,25):
            if lead%3==0:continue
            H=1+3**m*lead
            assert first.v3(H-1)==m
            for ell in range(2,m+4):
                Li=3**ell;L=Li+3*(H-1);tested+=1
                if first.v3(L)!=ell or (L//Li)%3!=1:continue
                assert ell<=m;accepted+=1
                if ell>2:
                    numerator=6*H+3-Li
                    assert first.v3(abs(numerator))==2
                    # B-1 is a3-adic unit, so any integral nonzero M1 has this valuation.
                    for B in (3,9,27,81):
                        assert (B-1)%3==2
                        if numerator%(B-1)==0:
                            M1=numerator//(B-1)
                            assert first.v3(abs(M1))==2<ell
                    long_obstructions+=1
    return dict(low_length_cases=tested,retained_least_marker_cases=accepted,
                longer_input_valuation_obstructions=long_obstructions,
                scope='Exact length and least-marker residues with arbitrary H leading units1/2. These are local valuation tests, not complete geometry or transport witnesses.')


def leading_radix_gate():
    integral=twos=boolean=0
    for m in range(3,9):
        for lead in range(1,49):
            if lead%3==0:continue
            H=1+3**m*lead
            for a in range(2,7):
                B=3**(a-1);numerator=6*(H-1)
                if numerator%(B-1):continue
                M1=numerator//(B-1);integral+=1
                assert first.v3(M1)==m+1 and (M1//3**(m+1))%3==lead%3
                if lead%3==2:
                    assert not generic.tag.boolean(M1);twos+=1
                if generic.tag.boolean(M1):
                    assert lead%3==1;boolean+=1
    assert twos and boolean
    return dict(integral_marker_quotients=integral,leading_two_rejections=twos,
                Boolean_marker_quotients=boolean,
                scope='Full integer quotients for the derived marker relation; no Boolean-H assumption or full-source claim is imposed.')


def local_guard_gate():
    words=forced=0
    for m in range(4,10):
        h=3**m
        qs=[sum(b*3**i for i,b in enumerate(bs)) for bs in product((0,1),repeat=m)]
        for c in range(3,m):
            j0=m-c
            for Q in qs:
                words+=1
                if (2*Q+1)%h:continue
                assert Q==(h-1)//2
                for tail in (0,1,2,5,13):
                    A=3**j0*(1+3*tail)
                    assert first.v3(A)==j0 and (A//3**j0)%3==1
                    G=(A+Q)%h
                    assert (G//3**j0)%3==2 and not generic.tag.boolean(G)
                    forced+=1
    return dict(Boolean_low_Q_words=words,forced_carry_guard_rejections=forced,
                scope='Exhausts the low Q words at six widths; if the selected marker is absent below h and AH has leading1 at j0, the guard trit is2. Higher H digits are not restricted.')


def complete_halting_witnesses():
    cases=app_count=0;branches=[0,0]
    for a in range(2,6):
        for app in product((0,1),repeat=a):
            c=generic.extended(generic.tag.constants(2,app));app_count+=1
            for Ni in (0,3):
                for exponent in (3,4,5):
                    A=3**exponent;R=c['C']*A;q=R;H=1
                    E=Ni//3
                    raw=dict(Gstar=A+1,Q=0,S0=1,S1=0,M0=9,M1=0,
                             Ebar=1-E,E=E,Nbar=4-Ni,N=Ni)
                    s=dict(F_Q=1,F_S1=1,F_T=E+1,F_E=E+1,F_Nfinal=1,
                           Nsum=4,A=A,R=R,q=q,H=H,L=9,Lfinal=3,
                           Ninit=Ni,Linit=9,alphaI=A-9,alphaH=6)
                    before=generic.old.run(omission.prefix(c)[0][:-3],s)
                    P=before[omission.prefix(c)[1]];scale=q**10;r=P+(scale-1)//2
                    s.update(r=r,betaP=scale-r)
                    out=generic.old.run(omission.prefix(c)[0],s)
                    out.update(K=9,pell_tr1=2*r+1)
                    assert all(out[x]==out[y] for x,y in omission.outer_comparisons())
                    assert all(v>0 for n,v in s.items() if n not in generic.PARAMETERS)
                    assert all(0<=v<q and generic.tag.boolean(v) for v in raw.values())
                    assert P==sum(raw[f]*q**i for i,f in enumerate(generic.FIELDS))
                    exponent_q=first.v3(q)
                    assert q==3**exponent_q and generic.old.unit.valuation(r)==10*exponent_q
                    assert generic.old.unit.mask_expected(r,10*exponent_q)
                    assert scale>=81 and 27<=r<scale and scale<r*r and R>=28*H
                    assert r%2==1
                    z=dict(raw,q=q,R=R,H=H,A=A,Ninit=Ni,Linit=9,
                           Nfinal=0,Lfinal=3,L=9)
                    assert first.check(c,z)['first_symbol']==0
                    initial=(0,Ni//3)
                    final=initial[2:]+(app if initial[0] else (0,))
                    assert final==(0,) and len(final)<2
                    cases+=1;branches[c['leading']]+=1
    return dict(appendants=app_count,complete_outer_witnesses=cases,
                leading_branch_cases=branches,outer_comparisons_per_tuple=9,
                conceptual_masks_per_tuple=10,actual_halting_steps=1,
                all_indices_odd=True,
                scope='Complete positive outer witnesses at H1 for the two actual one-step halting inputs, across all binary appendants of lengths2..5 and three widths. No beta2 nonpower-R example is claimed. Generic44 supplies the enormous positive Pell auxiliaries from the checked hypotheses.')


def verify():
    return dict(status='PASS_TAG_SHORT_GEOMETRY_SOUNDNESS',sources=symbolic(),
                least_marker=least_marker_gate(),leading_radix=leading_radix_gate(),
                local_guard=local_guard_gate(),witnesses=complete_halting_witnesses(),
                proof='../1980/EXPLORATION_TAG_SHORT_GEOMETRY_SOUNDNESS.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; proof and arithmetic frozen.',
                scope='Every complete weakened104 tuple with beta2,a>=2,R>=28H specifies input00 or01 and hence halts in one step. The size condition is a theorem hypothesis, not a free certificate comparison; unrestricted104 soundness and universal bounds remain open.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:v for k,v in result.items() if k not in ('sources','proof','review','scope')})
