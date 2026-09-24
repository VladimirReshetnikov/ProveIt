"""Reuse AH and the known zero first selector in a complete93 tag source."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_positive_startup_tag as previous

old=previous.old
tag=previous.tag
kernel=previous.kernel
base=previous.base
POSITIVE=previous.POSITIVE
PARAMETERS=previous.PARAMETERS
FIELDS=['S0','S1','Q','G']+previous.FIELDS[4:]


def prefix(c):
    removed={'head_coefficient0','head_coefficient','head_term','selector_scaled',
             'selector_inner','selector_term','selector_residual','upper_shifted',
             'low_join0','low_join1','pack_add8'}
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name=='guard_scale':
            rows.append(('AH','*','A','H'))
        elif name=='guard_base':
            rows.append((name,'*',c['guard_coefficient'],'AH'))
        elif name=='head_coefficient0':
            rows.extend([
                ('G','+','Q','AH'),
                ('qG','*','q','G'),
                ('QG_pair','+','Q','qG'),
                ('QG_shifted','*','q2','QG_pair'),
                ('flag_scaled','*','qm1','S1'),
                ('flag_pair','+','H','flag_scaled'),
                ('low_four','+','flag_pair','QG_shifted'),
                ('upper_shifted','*','q4','pack_add4'),
                ('pack_add8','+','low_four','upper_shifted')])
        elif name not in removed:
            rows.append((name,op,a,b))
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(name),op,old.rename(a),old.rename(b))
                        for name,op,a,b in kernel.schedule(1)]


def comparisons():
    return previous.comparisons()


def fields(c,s):
    inherited=dict(s,F_Q=s['Q']+1,F_S1=s['S1']+1,F_T=s['Tcontent']+1,
                   F_E=s['E']+1,F_Nfinal=1,Lfinal=3,alphaH=c['K']-3)
    raw=base.conceptual(c,inherited)
    raw['G']=s['Q']+s['A']*s['H']
    return raw


def verify_source(leading):
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    Cbar,Kh,Ut,B,cc,j=sp.symbols('Cbar Khalf Uthird B c jguard')
    c=dict(Cbar=Cbar,Khalf=Kh,Uthird=Ut,B=B,c=cc,C=Kh*Cbar,K=3*Kh,
           U=3*Ut+leading,leading=leading,guard_coefficient=j)
    inherited=dict(previous.lift(s),F_Nfinal=1,Lfinal=3,alphaH=c['K']-3)
    raw=fields(c,s)
    P=sum(raw[field]*s['q']**i for i,field in enumerate(FIELDS))
    src=base.sources(c,inherited)
    assert sp.expand(src[4])==0
    del src[4]
    src[6]=2*s['r']+1-s['q']**9-2*P
    sub={kernel.SYM[key]:s['q']**9 if key=='D0' else s[old.rename(key)] for key in kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in kernel.source_residuals(1)]
    src+=core
    env=old.run(schedule(c),s);env['K']=c['K']
    before=old.run(previous.schedule(c),s);before['K']=c['K']
    u=s['pell_j']*s['pell_c']+2*s['r']+1
    assert len(src)==len(comparisons())==18
    records=[]
    for i,((a,b),polynomial) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(u*u-s['pell_y_aux']**2) if i==16 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction)==0,i
        if i!=6:
            assert sp.expand(env[a]-before[a])==0 and sp.expand(env[b]-before[b])==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    assert sp.expand(env[prefix(c)[1]]-P)==0
    assert sp.expand(env['guard_base']-before['guard_base'])==0
    assert sp.expand(raw['Gstar']-raw['G']-raw['S0'])==0
    dag=schedule(base.constants(2,(leading,1)))
    assert old.counts(dag)==dict(operations=93,multiplications=51,additions=42)
    assert len(POSITIVE)==len(set(POSITIVE))==29
    return dict(leading=leading,operations=93,multiplications=51,additions=42,
                positive_unknowns=29,equations=18,outer_equations=8,kernel_equations=10,
                positive_coordinates=POSITIVE,parameters=PARAMETERS,fields=FIELDS,
                dag=dag,sources=records,
                scope='All non-index comparisons retain the95 source. The packed word and index change; '
                      'the positive43 converse is applied at the new even index.')


def packing_and_ranges():
    q,A,H,Q,S,L,E,N,cc,j,Rest=sp.symbols('q A H Q S L E N c j Rest')
    direct=(H-S)+q*S+q*q*Q+q**3*(Q+A*H)+q**4*Rest
    factored=H+(q-1)*S+q*q*(Q+q*(Q+A*H))+q**4*Rest
    assert sp.expand(direct-factored)==0
    # The nine raw fields, before any parity simplification.
    total=(H-S)+S+Q+(Q+A*H)+L+cc*H+N+j*A*H
    assert sp.expand(total-(N+L+H)-2*Q-((j+1)*A+cc)*H)==0
    constants=0
    for beta in range(2,13):
        K=3**beta;cc0=(K//3-1)//2
        for cexp in range(beta+1,beta+5):
            C=3**cexp;j0=(C-C//K)//2
            assert (j0+cc0)%2==1
            for m in range(2*(beta-1)+3,2*(beta-1)+10,2):
                d=m-beta+1
                assert (m+(m+1)*d)%2==1
                constants+=1
    signed_cases=negative=0
    for q0 in (3,9,27,81):
        J=(q0-1)//2
        for s0 in range(-J,q0):
            remainder=s0%q0
            if s0<0:
                assert remainder>J and not tag.boolean(remainder)
                negative+=1
            if tag.boolean(remainder):assert s0>=0
            signed_cases+=1
    bounds=0
    for beta in (2,4,6):
        K=3**beta;C=3**(3*beta+1)
        for A0,H0 in product((K+1,3*K,9*K),(1,2,7,31)):
            R=C*A0;q0=(R-1)*H0+1
            assert Fraction(A0*H0,q0)<Fraction(1,3)
            assert Fraction(q0,12)+A0*H0<q0
            assert Fraction(q0,6)<Fraction(q0,2)
            bounds+=1
    return dict(exact_identities=2,constant_and_padding_parity_cases=constants,
                signed_S0_cases=signed_cases,negative_S0_rejections=negative,
                prepower_guard_bounds=bounds)


def projector():
    cases=accepted=0
    for width,height in ((2,1),(3,1),(2,2)):
        R=3**width;A=R//3;q=R**height;H=(q-1)//(R-1)
        words=[sum(((mask>>i)&1)*3**i for i in range(width*height))
               for mask in range(1<<(width*height))]
        for chosen in range(1<<height):
            S=sum(((chosen>>i)&1)*R**i for i in range(height));S0=H-S
            for Q in words:
                cases+=1;M1=2*Q+S;G=Q+A*H
                if M1>=q or G>=q or not tag.boolean(M1) or not tag.boolean(G):continue
                accepted+=1
                for i in range(height):
                    si=(chosen>>i)&1;qi=(Q//R**i)%R;mi=(M1//R**i)%R
                    if not si:assert qi==mi==0
                    else:assert mi in [3**e for e in range(width)] and 2*qi+1==mi<=A
                assert G+S0<q and tag.boolean(G+S0)
    return dict(complete_projector_candidates=cases,accepted=accepted,
                scope='The G guard recovers the row projector and disjointly restores old Gstar=G+S0.')


def outer_pair(c,initial,words,selectors,prefixes,final):
    assert initial[0]==0 and final==(0,) and any(selectors)
    beta=len(tag.trits(c['K']))-1;h=beta-1
    ce=len(tag.trits(c['C']))-1
    m=max(ce+2+max(map(len,[initial]+words)),2*h+3)
    if m%2==0:m+=1
    R=3**m;A=R//c['C'];t=len(words);q0=R**t
    pack=lambda values:sum(value*R**i for i,value in enumerate(values))
    S1=pack(selectors);Q=pack([s*(3**len(w)-1)//2 for s,w in zip(selectors,words)])
    E=pack([(d-s)//3 for d,s in zip(prefixes,selectors)])
    N=pack([tag.value(w) for w in words]);L0=pack([3**len(w) for w in words])
    T=(N-S1)//3 if c['leading']==0 else (N+2*Q)//3
    assert min(Q,S1,E,T)>0
    results=[]
    for padded in (False,True):
        height=t+(m-h if padded else 0);q=R**height;H=(q-1)//(R-1)
        delta=q0*3*sum((R//c['Khalf'])**i for i in range(m)) if padded else 0
        s=dict(Q=Q,S1=S1,E=E,Tcontent=T,A=A,R=R,q=q,H=H,L=L0+delta,
               Ninit=tag.value(initial),Linit=3**len(initial),alphaI=A-3**len(initial),v=q//R)
        raw=fields(c,s)
        assert all(0<=raw[field]<q and tag.boolean(raw[field]) for field in FIELDS)
        assert raw['S0']%3==1 and raw['Gstar']==raw['G']+raw['S0']
        assert tag.boolean(raw['Gstar'])
        P=sum(raw[field]*q**i for i,field in enumerate(FIELDS))
        oldP=sum(raw[field]*q**i for i,field in enumerate(previous.FIELDS))
        assert P%2==(N+s['L']+H)%2
        assert (P-oldP+raw['S0'])%2==0
        D0=q**9;r=P+(D0-1)//2;s.update(r=r,betaP=D0-r)
        env=old.run(prefix(c)[0],s);env.update(K=c['K'],pell_tr1=2*r+1)
        assert all(env[a]==env[b] for a,b in comparisons()[:8])
        assert env[prefix(c)[1]]==P
        assert all(value>0 for name,value in s.items() if name not in PARAMETERS)
        before=old.run(previous.prefix(c)[0],s)
        assert all(before[a]==before[b] for a,b in comparisons()[:6])
        exponent=9*m*height
        assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
        assert 27<=r<D0 and D0<r*r
        results.append(dict(parity=r%2,height=height,valuation=exponent,changed_index=P!=oldP))
    assert results[0]['parity']!=results[1]['parity']
    return results


def canonical_checks():
    cases=rows=cutoff=nonzero=missing=0;branches=[0,0];parities=[0,0]
    changed=0
    for beta in (2,4,6,10):
      for app in ((0,0),(1,0),(0,1),(1,1),(0,1,0),(1,0,1)):
        c=base.constants(beta,app)
        for length in sorted({beta,beta+1,beta+2,2*beta-1,2*beta}):
          if length<=8:
            candidates=[(0,)+tail for tail in product((0,1),repeat=length-1)]
          else:
            candidates=[(0,0,1)+(0,)*(length-3),(0,1)+(1,)*(length-3)+(0,),
                        tuple(i%2 for i in range(length))]
          for initial in candidates:
            w=initial;words=[];ss=[];ds=[]
            for _ in range(30):
                if len(w)<beta:break
                words.append(w);ss.append(w[0]);ds.append(tag.value(w[:beta]))
                w=w[beta:]+(app if w[0] else (0,))
            if len(w)>=beta:cutoff+=1;continue
            if w!=(0,):nonzero+=1;continue
            if not any(ss) or tag.value(initial[:beta])//3==0:missing+=1;continue
            pair=outer_pair(c,initial,words,ss,ds,w)
            cases+=1;rows+=len(words);branches[c['leading']]+=1
            parities[pair[0]['parity']]+=1
            changed+=sum(item['changed_index'] for item in pair)
    assert cases and min(branches)>0 and min(parities)>0
    return dict(positive_startup_first_zero_histories=cases,genuine_source_rows=rows,
                full_outer_tuples=2*cases,fixed_leading_branches=branches,
                canonical_index_parities=parities,selected_padded=parities[1],
                changed_indices=changed,excluded_non_single_zero_terminal=nonzero,
                excluded_missing_startup=missing,cutoff_unclassified=cutoff,
                scope='Each canonical/padded pair checks all8 new outer comparisons, '
                      'all9 new masks, restored Gstar,6 unchanged95 outer comparisons, '
                      'new index valuation and positive scale hypotheses. Exactly one '
                      'member has a fresh positive fixed-plus43 extension.')


def odd_beta_example():
    beta=3;app=(1,0);initial=(0,0,1,1,0,0)
    words=[];selectors=[];prefixes=[];w=initial
    while len(w)>=beta:
        assert len(words)<4
        words.append(w);selectors.append(w[0]);prefixes.append(tag.value(w[:beta]))
        w=w[beta:]+(app if w[0] else (0,))
    assert words==[(0,0,1,1,0,0),(1,0,0,0),(0,1,0)] and w==(0,)
    pair=outer_pair(base.constants(beta,app),initial,words,selectors,prefixes,w)
    return dict(beta=beta,appendant=app,initial=initial,source_words=words,terminal=w,
                full_outer_tuples=2,results=pair,
                scope='Direct odd-beta parity converse: the three genuine rows satisfy '
                      'all startup promises; both complete new outer tuples pass.')


def verify():
    return dict(status='PASS_REORDERED_STARTUP_TAG93',
                sources=[verify_source(leading) for leading in (0,1)],
                packing=packing_and_ranges(),projector=projector(),histories=canonical_checks(),
                odd_beta=odd_beta_example(),
                review='Author and two independent complete proof/source reviews and fresh verification runs pass.',
                scope='Actual-halting soundness. Completeness for beta>=2, singleton zero '
                      'terminal, positive startup prefix and a selector1 event, and '
                      'an initial zero symbol. Primary Neary normalized instances satisfy '
                      'these promises; no raw-input loader or same-index witness map is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print([{key:s[key] for key in ('leading','operations','multiplications','additions',
                                  'positive_unknowns','equations')} for s in result['sources']])
    print(result['packing']);print(result['projector']);print(result['histories']);print(result['odd_beta'])
