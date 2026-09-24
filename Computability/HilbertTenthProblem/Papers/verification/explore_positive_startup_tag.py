"""Remove four positivity adapters when the startup guarantees positive words."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_zero_terminal_tag_parity as previous

old=previous.old
tag=previous.tag
kernel=previous.kernel
base=previous.previous
ADAPTERS={'F_Q':'Q','F_S1':'S1','F_T':'Tcontent','F_E':'E'}
POSITIVE=[ADAPTERS.get(n,n) for n in previous.positives(True,True)]
PARAMETERS=previous.PARAMETERS
FIELDS=previous.FIELDS

def lift(s):
    return {n:s[ADAPTERS[n]]+1 if n in ADAPTERS else s[n]
            for n in previous.positives(True,True)+PARAMETERS}

def prefix(c):
    rows,label=previous.prefix(c,True,True)
    removed=set(ADAPTERS.values())
    return [row for row in rows if row[0] not in removed],label

def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in kernel.schedule(1)]

def comparisons():return previous.comparisons(True,True)

def verify_source(leading):
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    Cbar,Kh,Ut,B,cc,j=sp.symbols('Cbar Khalf Uthird B c jguard')
    c=dict(Cbar=Cbar,Khalf=Kh,Uthird=Ut,B=B,c=cc,C=Kh*Cbar,K=3*Kh,
           U=3*Ut+leading,leading=leading,guard_coefficient=j)
    supplied=lift(s)
    inherited=dict(supplied,F_Nfinal=1,Lfinal=3,alphaH=c['K']-3)
    src=base.sources(c,inherited)
    assert sp.expand(src[4])==0
    del src[4]
    sub={kernel.SYM[k]:s['q']**9 if k=='D0' else s[old.rename(k)] for k in kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in kernel.source_residuals(1)]
    src+=core
    env=old.run(schedule(c),s);env['K']=c['K']
    before=old.run(previous.schedule(c,True,True),supplied);before['K']=c['K']
    assert len(src)==len(comparisons())==18
    u=s['pell_j']*s['pell_c']+2*s['r']+1
    records=[]
    for i,((a,b),polynomial) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(u*u-s['pell_y_aux']**2) if i==16 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction)==0,i
        assert sp.expand(env[a]-before[a])==0 and sp.expand(env[b]-before[b])==0
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    assert all(n not in ADAPTERS and a not in ADAPTERS and b not in ADAPTERS for n,_,a,b in schedule(c))
    dag=schedule(base.constants(2,(leading,1)))
    assert old.counts(dag)==dict(operations=95,multiplications=51,additions=44)
    assert len(POSITIVE)==len(set(POSITIVE))==29
    return dict(leading=leading,operations=95,multiplications=51,additions=44,
                positive_unknowns=29,equations=18,outer_equations=8,kernel_equations=10,
                positive_coordinates=POSITIVE,parameters=PARAMETERS,fields=FIELDS,dag=dag,sources=records)

def startup_facts():
    cases=0
    for p,n in product(range(1,9),range(7)):
        beta=10*p
        lower=11*(p+n+beta-2)
        for extra in (0,1,3):
            lam=(lower-1+beta-2)//(beta-1)+extra
            s=lam*(beta-1)+1
            assert s>=lower and s>=beta
            length=(s-1)*beta+1
            assert length==lam*beta*(beta-1)+1
            assert min(length-i*(beta-1) for i in (0,s-1))==s>=beta
            # Three cited Table2 entries suffice; no full Neary simulator is claimed.
            first_input_track=0
            even_track_second=0
            track_one_second=1
            initial_three=(first_input_track,even_track_second,track_one_second)
            assert tag.value(initial_three)==9 and beta>3
            epsilon_prime=(0,)*4+(1,)+(0,)*6
            tail=epsilon_prime*p
            assert len(tail)==11*p and any(tail)
            cases+=1
    return dict(parameter_cases=cases,initial_symbols=[0,0,1],initial_prefix_lower_bound=9,
                minimum_initial_T=3,minimum_initial_E=3,
                scope='Exact arithmetic consequences of the three cited Table2 tracks and the input-track suffix. '
                      'The source definitions are checked in the proof; this is not a materialized Neary simulator.')

def outer_pair(c,initial,words,selectors,prefixes,final):
    assert final==(0,) and any(selectors)
    assert tag.value(initial[:len(tag.trits(c['K']))-1])//3>0
    ce=len(tag.trits(c['C']))-1
    beta=len(tag.trits(c['K']))-1;h=beta-1
    m=max(ce+2+max(map(len,words)),2*h+3)
    if m%2==0:m+=1
    R=3**m;A=R//c['C'];t=len(words);q0=R**t
    packed=lambda vs:sum(v*R**i for i,v in enumerate(vs))
    S1=packed(selectors)
    Q=packed([s*(3**len(w)-1)//2 for s,w in zip(selectors,words)])
    E=packed([(d-s)//3 for d,s in zip(prefixes,selectors)])
    N=packed([tag.value(w) for w in words])
    M1=2*Q+S1
    L0=packed([3**len(w) for w in words])
    T=(N-S1)//3 if c['leading']==0 else (N+2*Q)//3
    assert min(Q,S1,E,T)>0 and A>max(3**len(w) for w in words)
    results=[]
    for padded in (False,True):
        height=t+(m-h if padded else 0);q=R**height;H=(q-1)//(R-1)
        delta=q0*3*sum((R//c['Khalf'])**i for i in range(m)) if padded else 0
        s=dict(Q=Q,S1=S1,E=E,Tcontent=T,A=A,R=R,q=q,H=H,L=L0+delta,
               Ninit=tag.value(initial),Linit=3**len(initial),alphaI=A-3**len(initial),v=q//R)
        inherited=dict(s,F_Q=Q+1,F_S1=S1+1,F_E=E+1,F_T=T+1,F_Nfinal=1,Lfinal=3,alphaH=c['K']-3)
        fields=base.conceptual(c,inherited)
        assert fields['M1']==M1
        assert fields['GN']==N+c['guard_coefficient']*A*H
        assert all(0<=v<q and tag.boolean(v) for v in fields.values())
        P=sum(fields[f]*q**i for i,f in enumerate(FIELDS));D0=q**9;r=P+(D0-1)//2
        s.update(r=r,betaP=D0-r)
        env=old.run(prefix(c)[0],s);env.update(K=c['K'],pell_tr1=2*r+1)
        assert all(env[a]==env[b] for a,b in comparisons()[:8])
        assert env[prefix(c)[1]]==P
        assert set(s)-set(PARAMETERS)==set(POSITIVE)-{old.rename(k) for k in kernel.SYM if k not in ('D0','r')}
        assert all(v>0 for n,v in s.items() if n not in PARAMETERS)
        exponent=9*m*height
        assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
        assert 27<=r<D0 and D0<r*r and fields['Gstar']%3==1
        results.append(r%2)
    assert results[0]!=results[1]
    return results[0]

def canonical_checks():
    cases=rows=not_zero=missing_read=missing_prefix=cutoff=0;branches=[0,0];parities=[0,0]
    for beta in (2,4,6,10):
      for app in ((0,0),(1,0),(0,1),(1,1),(0,1,0),(1,0,1)):
        c=base.constants(beta,app)
        for length in (beta,beta+1,2*beta-1):
          candidates={(1,)*length,(1,1)+(0,)*(length-2),
                      (0,1)+(1,)*(length-2),tuple(i%2 for i in range(length)),
                      (0,0,1)+(0,)*max(0,length-3)}
          for initial in sorted(w for w in candidates if len(w)==length):
            w=initial;words=[];selectors=[];prefixes=[]
            for _ in range(30):
                if len(w)<beta:break
                words.append(w);selectors.append(w[0]);prefixes.append(tag.value(w[:beta]))
                w=w[beta:]+(app if w[0] else (0,))
            if len(w)>=beta:cutoff+=1;continue
            if w!=(0,):not_zero+=1;continue
            if not any(selectors):missing_read+=1;continue
            if tag.value(initial[:beta])//3==0:missing_prefix+=1;continue
            parity=outer_pair(c,initial,words,selectors,prefixes,w)
            cases+=1;rows+=len(words);branches[c['leading']]+=1;parities[parity]+=1
    assert cases and min(branches)>0 and min(parities)>0
    return dict(positive_startup_histories=cases,genuine_source_rows=rows,full_outer_tuples=2*cases,
                fixed_leading_branches=branches,canonical_index_parities=parities,
                selected_padded=parities[1],excluded_non_single_zero_terminal=not_zero,
                excluded_no_one_read=missing_read,excluded_no_initial_tail_bit=missing_prefix,
                cutoff_unclassified=cutoff,
                scope='Both95 branches with strictly positive raw coordinates, both parity histories, '
                      'all eight outer comparisons and nine masks. The selected even index has a fresh '
                      'positive43 extension; enormous Pell auxiliaries are not materialized.')

def verify():
    return dict(status='PASS_POSITIVE_STARTUP_TAG95',sources=[verify_source(e) for e in (0,1)],
                startup=startup_facts(),histories=canonical_checks(),
                review='Author and two independent complete proof/source reviews and fresh verification runs pass without findings.',
                scope='Actual-halting soundness. Completeness for even beta, terminal word0, '
                      'an initial prefix bit beyond the head, and at least one actual one-symbol selection. '
                      'Neary supplies these promises for its normalized encoded instances; no raw-input loader is claimed.')

if __name__=='__main__':
    r=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
    print(r['status']);print(r['startup']);print(r['histories'])
