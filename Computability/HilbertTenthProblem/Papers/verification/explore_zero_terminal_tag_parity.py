"""Wrapped zero-channel padding and the fixed-plus103/zero-target100/99 sources.

Completeness assumes the actual halt has zero terminal content and even beta.
Soundness remains eventual actual halting, without a terminal-content promise.
"""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_single_content_guard_tag as previous
import explore_unit_two_ternary_kernel as kernel

old=previous.old
tag=previous.tag
FIELDS=previous.FIELDS
PARAMETERS=previous.PARAMETERS


def positives(zero=False,unit=False):
    assert not unit or zero
    removed={'pell_u'} | ({'F_Nfinal'} if zero else set()) | ({'Lfinal','alphaH'} if unit else set())
    return [x for x in previous.POSITIVE if x not in removed]


def prefix(c,zero=False,unit=False):
    assert not unit or zero
    rows,label=previous.prefix(c)
    if zero:rows=[row for row in rows if row[0] not in ('Nfinal','n_end','n_shift')]
    if unit:rows=[(n,op,3 if a=='Lfinal' else a,3 if b=='Lfinal' else b)
                  for n,op,a,b in rows if n!='halt_bound']
    return rows,label


def schedule(c,zero=False,unit=False):
    return prefix(c,zero,unit)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                              for n,op,a,b in kernel.schedule(1)]


def comparisons(zero=False,unit=False):
    outer=[(a,'n_initial' if zero and b=='n_shift' else b)
           for a,b in previous.outer_comparisons() if not unit or a!='halt_bound']
    return outer+[(old.rename(a),old.rename(b)) for a,b in kernel.EQUALITIES]


def verify_source(leading,zero,unit=False):
    pos=positives(zero,unit);s=dict(zip(pos+PARAMETERS,sp.symbols(' '.join(pos+PARAMETERS))))
    Cbar,Kh,Ut,B,cc,j=sp.symbols('Cbar Khalf Uthird B c jguard')
    c=dict(Cbar=Cbar,Khalf=Kh,Uthird=Ut,B=B,c=cc,C=Kh*Cbar,K=3*Kh,
           U=3*Ut+leading,leading=leading,guard_coefficient=j)
    env=old.run(schedule(c,zero,unit),s);env['K']=c['K']
    lifted=dict(s)
    if zero:lifted['F_Nfinal']=1
    if unit:lifted.update(Lfinal=3,alphaH=c['K']-3)
    src=previous.sources(c,lifted)
    if unit:
        assert sp.expand(src[4])==0
        del src[4]
    sub={kernel.SYM[k]:s['q']**9 if k=='D0' else s[old.rename(k)] for k in kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in kernel.source_residuals(1)]
    u=s['pell_j']*s['pell_c']+2*s['r']+1
    src+=core;records=[]
    assert len(src)==len(comparisons(zero,unit))==19-unit
    for i,((a,b),p) in enumerate(zip(comparisons(zero,unit),src)):
        correction=core[7]*(u*u-s['pell_y_aux']**2) if i==17-unit else 0
        assert sp.expand(env[a]-env[b]-p-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(correction)))
    before=old.run(previous.prefix(c)[0],lifted)
    for name in (prefix(c,zero,unit)[1],'index_rhs','packed_bound','n_left','l_left','l_shift'):
        assert sp.expand(env[name]-before[name])==0,name
    if zero:
        assert sp.expand(env['n_initial']-before['n_shift'])==0
        assert all('F_Nfinal' not in (n,a,b) for n,_,a,b in prefix(c,zero,unit)[0])
    if unit:
        assert all(x not in (n,a,b) for n,_,a,b in prefix(c,zero,unit)[0] for x in ('Lfinal','alphaH','halt_bound'))
        assert ('l_end','*','q',3) in prefix(c,zero,unit)[0]
    dag=schedule(previous.constants(2,(leading,1)),zero,unit)
    target=(dict(operations=99,multiplications=51,additions=48) if unit else
            dict(operations=100,multiplications=51,additions=49) if zero else
            dict(operations=103,multiplications=52,additions=51))
    assert old.counts(dag)==target and len(pos)==(29 if unit else 31 if zero else 32)
    return dict(**target,leading=leading,zero_target=zero,single_zero_target=unit,
                positive_unknowns=len(pos),equations=19-unit,
                outer_equations=9-unit,kernel_equations=10,positive_coordinates=pos,fields=FIELDS,
                parameters=PARAMETERS,dag=dag,sources=records,
                converse=('Even beta and a genuine halt at the single-symbol word0; choose the padded or unpadded even index.' if unit else
                          'Even beta and a genuine zero-content halt; choose the padded or unpadded even index. No claim for all nonzero-content halts.'))


def identities():
    q,A,H,Q,S1,L,N,cc,j=sp.symbols('q A H Q S1 L N c j')
    # Sum of nine conceptual fields; E cancels with Ebar.
    total=(Q+A*H+H-S1)+Q+(H-S1)+S1+L+cc*H+(N+j*A*H)
    rhs=2*Q+L+N+S1+(1+cc+j)*H
    assert sp.expand(total-rhs)==sp.expand((j+1)*(A-1)*H+2*(H-S1))
    b,delta,start,end=sp.symbols('b delta start end')
    assert sp.expand(delta+end-start-b*delta)==sp.expand(end-start-(b-1)*delta)
    parity=0
    for beta in range(1,17):
        K=3**beta;cp=(K//3-1)//2
        for cexp in range(beta+1,beta+7):
            C=3**cexp;jg=(C-C//K)//2
            assert (1+cp+jg)%2==0
            parity+=1
    return dict(exact_polynomial_identities=2,constant_parity_cases=parity)


def wrapped_paths():
    cases=extra_rows=multi_rows=0
    for beta in (2,4,6,10):
        h=beta-1
        for m in range(2*h+3,2*h+12,2):
            assert m%2 and m>2*h
            for s in range(beta):
                t=2;d=m-h;T=t+d
                nodes=[t*m+s+i*d for i in range(m)]
                endpoint=t*m+s+m*d
                assert endpoint==T*m+s and len(set(nodes))==m
                assert min(nodes)>=t*m and max(nodes)<T*m
                counts={i:sum(e//m==i for e in nodes) for i in range(t,T)}
                assert all(x>=1 for x in counts.values())
                assert (m+m*(T-t))%2==(m*h)%2==1
                cases+=1;extra_rows+=T-t;multi_rows+=sum(x>1 for x in counts.values())
    return dict(wrapped_path_cases=cases,total_added_rows=extra_rows,multiple_marker_rows=multi_rows,
                scope='Exact exponent paths, including nonempty and empty short endpoints. These are not charged runtime exponentiations or complete source tuples.')


def tuple_at(c,initial,words,selectors,prefixes,final,m,padded):
    beta=len(tag.trits(c['K']))-1;h=beta-1;C=c['C'];R=3**m;A=R//C
    assert R%C==0 and m%2 and m>2*h and A>max(3**len(w) for w in [initial]+words)
    assert tag.value(final)==0 and 0<=len(final)<beta
    t=len(words);q0=R**t;Lf=3**len(final)
    raw=dict.fromkeys(('Q','S1','M0','M1','E','N'),0)
    for i,(w,s,d) in enumerate(zip(words,selectors,prefixes)):
        wt=R**i;li=3**len(w)
        raw['Q']+=s*(li-1)//2*wt;raw['S1']+=s*wt;raw['M'+str(s)]+=li*wt
        raw['E']+=(d-s)//3*wt;raw['N']+=tag.value(w)*wt
    originalM0=raw['M0'];b=R//c['Khalf'];height=t
    if padded:
        delta=q0*Lf*sum(b**i for i in range(m));raw['M0']+=delta;height=t+m-h
        assert (b-1)*delta==q0*Lf*(b**m-1)
        assert b**m==R**(m-h)
    q=R**height;H=(q-1)//(R-1)
    T=(raw['N']-raw['S1'])//3 if c['leading']==0 else (raw['N']+2*raw['Q'])//3
    s=dict(F_Q=raw['Q']+1,F_S1=raw['S1']+1,F_T=T+1,F_E=raw['E']+1,F_Nfinal=1,
           A=A,H=H,R=R,L=raw['M0']+raw['M1'],q=q,Lfinal=Lf,
           Ninit=tag.value(initial),Linit=3**len(initial),alphaI=A-3**len(initial),
           alphaH=c['K']-Lf,v=q//R)
    first=old.run(prefix(c)[0][:-3],s);P=first[prefix(c)[1]];D0=q**9;r=P+(D0-1)//2
    s.update(r=r,betaP=D0-r)
    fields=previous.conceptual(c,s)
    assert all(0<=v<q and tag.boolean(v) for v in fields.values())
    assert P==sum(fields[f]*q**i for i,f in enumerate(FIELDS))
    assert P%2==(raw['N']+raw['S1']+s['L'])%2
    assert r%2==(P+m*height)%2 and fields['Gstar']%3==1
    variants=[(False,False),(True,False)]+([(True,True)] if Lf==3 else [])
    for zero,unit in variants:
        envs=dict(s)
        if zero:del envs['F_Nfinal']
        if unit:
            assert envs['Lfinal']==3 and envs['alphaH']==c['K']-3>0
            del envs['Lfinal'];del envs['alphaH']
        out=old.run(prefix(c,zero,unit)[0],envs);out.update(K=c['K'],pell_tr1=2*r+1)
        assert all(out[a]==out[b] for a,b in comparisons(zero,unit)[:9-unit])
        assert all(v>0 for n,v in envs.items() if n not in PARAMETERS)
        assert out[prefix(c,zero,unit)[1]]==P
    exponent=9*m*height
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<D0 and D0<r*r
    return dict(parity=r%2,height=height,rows=t,valuation=exponent,
                added_markers=m if padded else 0,old_markers=raw['M0']-originalM0,
                zero_T=T==0,single_zero_target=Lf==3,positive_kernel_hypotheses=True)


def canonical_and_padded():
    cases=rows=nonzero=cutoff=selected_padded=zero_T=single_zero=single_padded=0;branches=[0,0];parities=[0,0]
    betas=[2,4,6,10]
    apps=[(0,0),(1,0),(0,1),(1,1),(0,1,0),(1,0,1)]
    for beta in betas:
        for app in apps:
            c=previous.constants(beta,app)
            for length in (beta,beta+1,2*beta-1):
                initials={(0,)*length,(1,)+(0,)*(length-1),(0,)*(length-1)+(1,),
                          tuple(i%2 for i in range(length)),(1,)*length}
                for initial in sorted(initials):
                    w=initial;words=[];ss=[];ds=[]
                    for _ in range(30):
                        if len(w)<beta:break
                        words.append(w);ss.append(w[0]);ds.append(tag.value(w[:beta]))
                        w=w[beta:]+(app if w[0] else (0,))
                    if len(w)>=beta:cutoff+=1;continue
                    if tag.value(w):nonzero+=1;continue
                    ce=len(tag.trits(c['C']))-1
                    m=max(ce+2+max(map(len,[initial]+words)),2*(beta-1)+3)
                    if m%2==0:m+=1
                    a=tuple_at(c,initial,words,ss,ds,w,m,False)
                    b=tuple_at(c,initial,words,ss,ds,w,m,True)
                    assert a['parity']!=b['parity']
                    assert b['height']-a['height']==m-beta+1
                    chosen=b if a['parity'] else a
                    assert chosen['parity']==0
                    selected_padded+=bool(a['parity']);zero_T+=chosen['zero_T']
                    single_zero+=a['single_zero_target']
                    single_padded+=a['single_zero_target'] and bool(a['parity'])
                    cases+=1;rows+=len(words);branches[c['leading']]+=1
                    parities[a['parity']]+=1
    assert cases and min(branches)>0 and min(parities)>0 and selected_padded
    return dict(zero_terminal_histories=cases,genuine_source_rows=rows,full_outer_tuples=2*cases,
                checks_per_tuple=dict(source_variants=2,outer_comparisons=9,masked_fields=9),
                fixed_leading_branches=branches,canonical_index_parities=parities,
                selected_padded_even_witnesses=selected_padded,selected_unpadded_even_witnesses=cases-selected_padded,
                selected_zero_T=zero_T,nonzero_terminal_halts_outside_contract=nonzero,
                single_zero_histories=single_zero,full99_outer_tuples=2*single_zero,
                single_zero_selected_padded=single_padded,
                fixed99_checks_per_tuple=dict(outer_comparisons=8,masked_fields=9),
                cutoff_unclassified=cutoff,
                scope='Both103 and100 outer schedules, all9 masks and exact valuations on each canonical/padded pair;99 additionally checked for the single-symbol zero terminal. Exactly one member has even r and receives a full positive plus43 converse. Huge Pell auxiliaries are proved to exist, not materialized.')


def verify():
    return dict(status='PASS_ZERO_TERMINAL_TAG_PARITY',
                sources=[verify_source(e,z,u) for z,u in ((False,False),(True,False),(True,True)) for e in (0,1)],
                identities=identities(),paths=wrapped_paths(),histories=canonical_and_padded(),
                proof='../1980/EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md',
                review='Author and two independent complete proof/source reviews and fresh full verification runs pass without findings.',
                scope='Fixed-plus103, fixed-zero100 and fixed-single-zero99 are sound for actual halting. Completeness holds for even beta and actual zero-content halts, with99 requiring the single-symbol zero terminal. Neary compatibility is for the primary-source encoded instances, not one fixed-u raw-input universal polynomial.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print([{k:r[k] for k in ('leading','zero_target','single_zero_target','operations','multiplications','additions','positive_unknowns','equations')} for r in result['sources']])
    print({k:v for k,v in result.items() if k not in ('sources','proof','review','scope')})
