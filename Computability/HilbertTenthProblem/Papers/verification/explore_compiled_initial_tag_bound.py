"""Absorb the admitted initial-length bound into the fixed compiler constant.

This is semantic equivalence on K^2*Linit<C, not a positive alphaI lift for
arbitrary solutions. The initial encoded word is not changed.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_reordered_startup_tag as previous

old=previous.old
tag=previous.tag
kernel=previous.kernel
base=previous.base
PARAMETERS=previous.PARAMETERS
FIELDS=previous.FIELDS
POSITIVE=[name for name in previous.POSITIVE if name!='alphaI']


def constants(beta,app):
    c=base.constants(beta,app)
    bound=max(c['K']**3,3*c['K']*3**len(app),2*c['K']*c['U']+3)
    C=c['C']
    while C<=bound:C*=3
    c.update(C=C,Cbar=C//c['Khalf'],guard_coefficient=(C-C//c['K'])//2)
    return c


def prefix(c):
    rows,label=previous.prefix(c)
    return [row for row in rows if row[0]!='initial_bound'],label


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in kernel.schedule(1)]


def comparisons():
    return [pair for pair in previous.comparisons() if pair[0]!='initial_bound']


def verify_source(leading):
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    Cbar,Kh,Ut,B,cc,j=sp.symbols('Cbar Khalf Uthird B c jguard')
    c=dict(Cbar=Cbar,Khalf=Kh,Uthird=Ut,B=B,c=cc,C=Kh*Cbar,K=3*Kh,
           U=3*Ut+leading,leading=leading,guard_coefficient=j)
    # This formal substitution can be signed. It proves source identities,
    # not a positive inverse witness map.
    lifted=dict(s,alphaI=s['A']-s['Linit'])
    inherited=dict(previous.previous.lift(lifted),F_Nfinal=1,Lfinal=3,alphaH=c['K']-3)
    raw=previous.fields(c,lifted)
    P=sum(raw[f]*s['q']**i for i,f in enumerate(FIELDS))
    src=base.sources(c,inherited)
    assert sp.expand(src[3])==sp.expand(src[4])==0
    del src[4];del src[3]
    src[5]=2*s['r']+1-s['q']**9-2*P
    sub={kernel.SYM[k]:s['q']**9 if k=='D0' else s[old.rename(k)] for k in kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in kernel.source_residuals(1)]
    src+=core
    env=old.run(schedule(c),s);env['K']=c['K']
    before=old.run(previous.schedule(c),lifted);before['K']=c['K']
    u=s['pell_j']*s['pell_c']+2*s['r']+1
    assert len(src)==len(comparisons())==17
    records=[]
    for i,((a,b),polynomial) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(u*u-s['pell_y_aux']**2) if i==15 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction)==0,i
        assert sp.expand(env[a]-before[a])==sp.expand(env[b]-before[b])==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    assert sp.expand(env[prefix(c)[1]]-P)==0
    dag=schedule(constants(2,(leading,1)))
    assert old.counts(dag)==dict(operations=92,multiplications=51,additions=41)
    assert len(POSITIVE)==len(set(POSITIVE))==28
    assert all('alphaI' not in (n,a,b) and n!='initial_bound' for n,op,a,b in dag)
    assert ('l_end','*','q',3) in dag
    return dict(leading=leading,operations=92,multiplications=51,additions=41,
                positive_unknowns=28,equations=17,outer_equations=7,kernel_equations=10,
                positive_coordinates=POSITIVE,parameters=PARAMETERS,fields=FIELDS,
                dag=dag,sources=records,
                scope='The signed formal alphaI substitution proves polynomial equality only; '
                      'soundness is proved directly on the admitted domain K^2*Linit<C.')


def prepower_bounds():
    cases=unit=negative_slacks=zero_slacks=nonpower=0
    for beta in (2,3,4,10):
      for a in (3*beta-2,4*beta-3):
       Li=3**(a-beta+1);Ni=(Li-1)//2
       for app in ((0,)*a,(1,)*a):
        c=constants(beta,app);K=c['K'];k=c['Khalf'];C=c['C'];B=c['B'];U=c['U']
        assert C>K*K*Li and C>max(K**3,3*K*3**a,2*K*U+3)
        for A,H in product((1,2,3,Li,Li+1,3*Li),(1,2,7,31)):
            R=C*A;q=(R-1)*H+1
            Lbound=Fraction(k*K*q,R-k)
            Mbound=Fraction(k*K*q,R*(B-1))
            Jg=Fraction((R-R//K)*H,2)
            input_bound=Fraction(K*Ni,R)
            assert q>=R>K*K and q>108 and K*K*Li<R
            assert Fraction(R,k)>Li
            assert Lbound<Fraction(q,2) and Mbound<Fraction(q,6)
            assert Jg>=Fraction(q-1,3) and Jg-Mbound>0
            assert input_bound<Fraction(1,2*K)
            assert U*Mbound<Fraction(3*q,4)
            Ebound=(Fraction(q-1,2)+U*Mbound+input_bound)/3
            assert Ebound<Fraction(q,2)
            assert Mbound/2+A*H<q and Fraction(c['c']*H,q)<Fraction(1,2)
            cases+=1;unit+=A==1;negative_slacks+=A<Li;zero_slacks+=A==Li
            nonpower+=sum(tag.trits(R))!=1 or sum(tag.trits(q))!=1
    return dict(prepower_cases=cases,A_one_cases=unit,negative_formal_alphaI=negative_slacks,
                zero_formal_alphaI=zero_slacks,nonpower_R_or_q=nonpower,
                scope='Exact rational consequences of the weakened positive geometry and length/content bounds. '
                      'These are not complete source tuples; no radix-power or digit filter is used.')


def exclude_unit_A():
    cases=accepted=0
    for width,height in product((2,3,4),(1,2)):
        R=3**width;q=R**height;H=(q-1)//(R-1)
        for mask in range(1<<height):
            S1=sum(((mask>>i)&1)*R**i for i in range(height))
            for bits in range(1<<(width*height)):
                Q=sum(((bits>>i)&1)*3**i for i in range(width*height))
                G=Q+H;M1=2*Q+S1;cases+=1
                if G>=q or M1>=q or not(tag.boolean(G) and tag.boolean(M1)):continue
                assert Q==0 and M1==S1 and G==H
                accepted+=1
    return dict(complete_A_one_mask_candidates=cases,admitted_Q_zero=accepted,
                admitted_positive_Q=0,
                scope='Complete small global-word enumeration; the proof excludes A=1 at every height.')


def outer_pair(c,initial,words,selectors,prefixes,final):
    assert initial[0]==0 and final==(0,) and any(selectors)
    beta=len(tag.trits(c['K']))-1;h=beta-1;Li=3**len(initial)
    assert c['K']**2*Li<c['C']
    ce=len(tag.trits(c['C']))-1
    m=max(ce+2+max(map(len,[initial]+words)),2*h+3)
    if m%2==0:m+=1
    R=3**m;A=R//c['C'];t=len(words);q0=R**t
    pack=lambda vs:sum(v*R**i for i,v in enumerate(vs))
    S1=pack(selectors);Q=pack([si*(3**len(w)-1)//2 for si,w in zip(selectors,words)])
    E=pack([(d-si)//3 for d,si in zip(prefixes,selectors)])
    N=pack([tag.value(w) for w in words]);L0=pack([3**len(w) for w in words])
    T=(N-S1)//3 if c['leading']==0 else (N+2*Q)//3
    assert min(Q,S1,E,T)>0
    answer=[]
    for padded in (False,True):
        height=t+(m-h if padded else 0);q=R**height;H=(q-1)//(R-1)
        delta=q0*3*sum((R//c['Khalf'])**i for i in range(m)) if padded else 0
        s=dict(Q=Q,S1=S1,E=E,Tcontent=T,A=A,R=R,q=q,H=H,L=L0+delta,
               Ninit=tag.value(initial),Linit=Li,v=q//R)
        chosen_lift=dict(s,alphaI=A-Li)
        assert chosen_lift['alphaI']>0
        raw=previous.fields(c,chosen_lift)
        assert all(0<=raw[f]<q and tag.boolean(raw[f]) for f in FIELDS)
        assert raw['S0']%3==1 and tag.boolean(raw['Gstar'])
        P=sum(raw[f]*q**i for i,f in enumerate(FIELDS));D0=q**9;r=P+(D0-1)//2
        s.update(r=r,betaP=D0-r);chosen_lift.update(r=r,betaP=D0-r)
        env=old.run(prefix(c)[0],s);env.update(K=c['K'],pell_tr1=2*r+1)
        before=old.run(previous.prefix(c)[0],chosen_lift);before.update(K=c['K'],pell_tr1=2*r+1)
        assert all(env[a]==env[b] for a,b in comparisons()[:7])
        assert all(before[a]==before[b] for a,b in previous.comparisons()[:8])
        assert env[prefix(c)[1]]==before[previous.prefix(c)[1]]==P
        assert all(v>0 for name,v in s.items() if name not in PARAMETERS)
        exponent=9*m*height
        assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
        assert 27<=r<D0 and D0<r*r
        answer.append(dict(parity=r%2,height=height,valuation=exponent,preserved_index=True))
    assert answer[0]['parity']!=answer[1]['parity']
    return answer


def canonical_checks():
    cases=rows=nonzero=missing=cutoff=odd_beta=0;branches=[0,0];parities=[0,0]
    for beta in (2,3,4,10):
      for a in (3*beta-2,4*beta-3):
        ell=a-beta+1
        structured=[0]*ell;structured[1]=structured[beta]=1
        inputs={tuple(structured),(0,)+(1,)*(ell-1)}
        for app in ((0,)*a,(1,)+(0,)*(a-1),(0,1)+(0,)*(a-2)):
          c=constants(beta,app)
          for initial in sorted(inputs):
            words=[];ss=[];ds=[];w=initial
            for _ in range(80):
                if len(w)<beta:break
                words.append(w);ss.append(w[0]);ds.append(tag.value(w[:beta]))
                w=w[beta:]+(app if w[0] else (0,))
            if len(w)>=beta:cutoff+=1;continue
            if w!=(0,):nonzero+=1;continue
            if not any(ss) or tag.value(initial[:beta])//3==0:missing+=1;continue
            pair=outer_pair(c,initial,words,ss,ds,w)
            cases+=1;rows+=len(words);branches[c['leading']]+=1;odd_beta+=beta%2
            parities[pair[0]['parity']]+=1
    assert cases and min(branches)>0 and min(parities)>0 and odd_beta
    return dict(admitted_histories=cases,genuine_source_rows=rows,full_outer_tuples=2*cases,
                fixed_leading_branches=branches,canonical_index_parities=parities,
                selected_padded=parities[1],odd_beta_histories=odd_beta,
                excluded_non_single_zero_terminal=nonzero,excluded_missing_startup=missing,
                cutoff_unclassified=cutoff,
                scope='Each pair has K^2*Linit<C and the fixed-length relation Linit=3^(a-beta+1). '
                      'Checks all7 new and8 chosen positive-lift outer comparisons,9 masks and exact '
                      'valuations. Exactly one member has the proved positive plus43 extension; '
                      'huge Pell auxiliaries are not materialized. These are ordinary finite tag examples, '
                      'not materialized Neary simulators.')


def verify():
    return dict(status='PASS_COMPILED_INITIAL_TAG_BOUND92',
                sources=[verify_source(e) for e in (0,1)],prepower=prepower_bounds(),
                unit_A=exclude_unit_A(),histories=canonical_checks(),
                proof='../1980/EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs pass.',
                scope='Actual-halting soundness on K^2*Linit<C. Completeness on that domain with '
                      'the positive-startup, initial-zero and single-zero-terminal promises of93. '
                      'Neary fixed encoded lengths satisfy the domain by the stronger free C. '
                      'No same-witness positive alphaI inverse or raw-input universal bound is claimed.')


if __name__=='__main__':
    r=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
    print(r['status']);print([{k:s[k] for k in ('leading','operations','multiplications','additions','positive_unknowns','equations')} for s in r['sources']])
    print(r['prepower']);print(r['unit_A']);print(r['histories'])
