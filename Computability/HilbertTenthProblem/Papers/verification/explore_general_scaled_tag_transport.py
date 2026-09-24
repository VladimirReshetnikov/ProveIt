"""Generic105: fixed appendant-leading-bit choice and a signed N bootstrap."""
from itertools import product
from pathlib import Path
from fractions import Fraction
import json
import sympy as sp
import explore_shared_marker_low_packing as previous

old=previous.old
tag=previous.tag
FIELDS=previous.FIELDS
PARAMETERS=previous.PARAMETERS
POSITIVE=['F_T' if x=='F_N' else x for x in previous.POSITIVE]


def extended(c):
    d=dict(c)
    if isinstance(c['C'],int):
        assert c['C']%c['Khalf']==0 and c['U']%3 in (0,1)
        d.update(Cbar=c['C']//c['Khalf'],Uthird=c['U']//3,leading=c['U']%3)
    return d


def prefix(c):
    c=extended(c);assert c['leading'] in (0,1)
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name=='N':
            rows += [('Tcontent','-','F_T',1),('three_T','*',3,'Tcontent')]
        elif name=='radix':
            rows += [('transport_scale','*',c['Cbar'],'A'),('radix','*',c['Khalf'],'transport_scale')]
        elif name in ('prefix_tail','d','n_right','l_right'):continue
        elif name=='n_trim':rows.append((name,'-','Tcontent','E'))
        elif name=='n_append':rows.append((name,'*',c['Uthird'],'M1'))
        elif name in ('n_left','l_left'):rows.append((name,'*','transport_scale',b))
        else:rows.append((name,op,a,b))
        if name=='twice_Q':
            rows.append(('N','+' if c['leading']==0 else '-',
                         'three_T','S1' if c['leading']==0 else 'twice_Q'))
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in old.kernel.SCHEDULE]


def outer_comparisons():
    return [(a,'n_shift' if b=='n_right' else 'l_shift' if b=='l_right' else b)
            for a,b in previous.outer_comparisons()]


def comparisons():
    return outer_comparisons()+[(old.rename(a),old.rename(b)) for a,b in old.kernel.EQUALITIES]


def content_coordinate(c,s):
    T,Q,S1=s['F_T']-1,s['F_Q']-1,s['F_S1']-1
    return 3*T+S1 if c['leading']==0 else 3*T-2*Q


def sources(c,s):
    N=content_coordinate(c,s);T,E=s['F_T']-1,s['F_E']-1
    M1=2*(s['F_Q']-1)+s['F_S1']-1
    src=previous.sources(c,dict(s,F_N=N+1))
    src[2]=c['Cbar']*s['A']*(T-E+c['Uthird']*M1)-(N-s['Ninit']+s['q']*(s['F_Nfinal']-1))
    src[3]=c['Cbar']*s['A']*(s['L']+(c['B']-1)*M1)-(s['L']-s['Linit']+s['q']*s['Lfinal'])
    return src


def verify_source_branch(leading):
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    Cbar,Kh,Ut,B,cc=sp.symbols('Cbar Khalf Uthird B c')
    c=dict(Cbar=Cbar,Khalf=Kh,Uthird=Ut,B=B,c=cc,C=Kh*Cbar,K=3*Kh,U=3*Ut+leading,leading=leading)
    env=old.run(schedule(c),s);env['K']=c['K'];src=sources(c,s)
    sub={old.kernel.SYM[k]:s['q']**10 if k=='D0' else s[old.rename(k)] for k in old.kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in old.kernel.source_residuals()]
    src+=core;records=[]
    assert len(src)==len(comparisons())==21
    for i,((a,b),p) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i==18 else 0
        assert sp.expand(env[a]-env[b]-p-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(correction)))
    former=dict(s,F_N=content_coordinate(c,s)+1)
    before=old.run(previous.prefix(c)[0],former);oldsrc=previous.sources(c,former)
    assert sp.expand(oldsrc[2]-3*Kh*src[2]+3*src[0]*env['n_output'])==0
    assert sp.expand(oldsrc[3]-Kh*src[3]+src[0]*env['l_output'])==0
    for i in set(range(10))-{2,3}:assert sp.expand(oldsrc[i]-src[i])==0,i
    for name in ('N','radix',prefix(c)[1],'index_rhs','packed_bound'):
        assert sp.expand(env[name]-before[name])==0,name
    for removed in ('F_N','prefix_tail','d','n_right','l_right'):
        assert all(removed not in (n,a,b) for n,_,a,b in prefix(c)[0])
    dag=schedule(tag.constants(2,(leading,1)))
    assert old.counts(dag)==dict(operations=105,multiplications=53,additions=52)
    assert len(POSITIVE)==len(set(POSITIVE))==34
    assert sum(n=='twice_Q' for n,_,_,_ in prefix(c)[0])==1
    return dict(**old.counts(dag),positive_unknowns=34,equations=21,outer_equations=10,kernel_equations=11,
                leading=leading,positive_coordinates=POSITIVE,parameters=PARAMETERS,fields=FIELDS,
                dag=dag,sources=records,
                former_coordinate='F_N=3F_T+F_S1-3' if leading==0 else 'F_N=3F_T-2F_Q',
                source_embedding='Both old transport sources are scaled new sources plus a multiple of the retained radix source; other sources and packing match exactly.')


def finite_identities():
    cases=negative=0
    for leading in (0,1):
        for Kh,Cbar,A,R,Q,T,S1,E,Ut in product((1,3),(3,9),(5,), (14,45), (0,2),(0,1),(0,2),(0,3),(0,1,4)):
            M1=2*Q+S1;D=Cbar*A;N=3*T+S1 if leading==0 else 3*T-2*Q
            q,Ni,Nf,L,Li,Lf,B=17,2,1,7,9,3,9
            O=T-E+Ut*M1;shift=N-Ni+q*Nf;f0=Kh*D-R
            oldC=R*(N-3*E-S1+(3*Ut+leading)*M1)-3*Kh*shift
            newC=D*O-shift;OL=L+(B-1)*M1
            oldL=R*OL-Kh*(L-Li+q*Lf);newL=D*OL-(L-Li+q*Lf)
            assert oldC==3*Kh*newC-3*f0*O and oldL==Kh*newL-f0*OL
            cases+=1;negative+=N<0
    return dict(off_shell_cases=cases,negative_content_cases=negative,
                scope='Both fixed compile-time branches, failed radix geometry, nonpower q and signed reconstructed N; these are polynomial identities, not complete source tuples.')


def bootstrap_and_negative_pairs():
    arithmetic=negative=mask_rejections=0
    for q in (3,5,7,9,11,27,81,243):
        D=q**10
        assert Fraction(11*D,36)-Fraction(1,2)>Fraction(D,4)
        assert D>81 and Fraction(D,4)>27 and (Fraction(D,4))**2>D
        assert q**3-q*q-1>0
        if q>4:assert Fraction(7*q,24)+Fraction(1,6)<Fraction(q,3)
        arithmetic+=1
    for q in (9,27,81,243):
        scale=q**10;wide=(scale-1)//2;exponent=len(tag.trits(scale))-1
        for Ns in range(1,(q-1)//4+1):
            for N in range(-((7*q-1)//36),0):
                for base,E,lo in product((0,1,q-1),(0,(q-1)//3),(1,q**6-1)):
                    TN=Ns+(q-1)*N;TE=base+(q-1)*E
                    assert TN<-1 and 0<=TE<q*q
                    P=lo+q**6*TE+q**8*TN;r=wide+P
                    assert 0<lo+q**6*TE<q**8 and P<0
                    assert Fraction(scale,4)<r<wide
                    assert not old.unit.mask_expected(r,exponent)
                    assert old.unit.valuation(r)<exponent
                    negative+=1;mask_rejections+=1
    return dict(rational_bootstrap_cases=arithmetic,negative_pair_cases=negative,
                exact_native_mask_rejections=mask_rejections,
                scope='The proved N<0/E<q/3 ranges, sampled extremal prefix bases and lower blocks. These necessary-range states need not satisfy all tag sources; their negative P and failed valuation are checked exactly.')


def witness(beta,app,initial,words,ss,ds,final):
    assert len(app)>=2
    c=extended(tag.constants(beta,app));leading=c['leading']
    A=3**(1+max([len(initial)]+[len(w) for w in words]));R=c['C']*A
    t=len(words);q=R**t;H=(q-1)//(R-1);raw=dict.fromkeys(old.RAW,0)
    for j,(w,sel,d) in enumerate(zip(words,ss,ds)):
        wt=R**j;mark=3**len(w);n=tag.value(w);ns=(mark-1)//2
        assert n>=sel and n%3==sel and len(w)>=beta
        raw['Q']+=sel*ns*wt;raw['S'+str(sel)]+=wt;raw['M'+str(sel)]+=mark*wt
        raw['N']+=n*wt;raw['Nbar']+=(ns-n)*wt
        e=(d-sel)//3;raw['E']+=e*wt;raw['Ebar']+=(c['c']-e)*wt
    numerator=raw['N']-raw['S1'] if leading==0 else raw['N']+2*raw['Q']
    assert numerator>=0 and numerator%3==0
    T=numerator//3
    env={'F_'+x:raw[x]+1 for x in previous.RAW if x!='N'}
    env.update(F_T=T+1,Nsum=raw['N']+raw['Nbar'],F_Nfinal=tag.value(final)+1,
               A=A,R=R,q=q,H=H,L=raw['M0']+raw['M1'],Lfinal=3**len(final),
               Ninit=tag.value(initial),Linit=3**len(initial),alphaI=A-3**len(initial),
               alphaH=c['K']-3**len(final),v=q//R)
    first=old.run(prefix(c)[0][:-3],env);P=first[prefix(c)[1]]
    scale=q**10;r=P+(scale-1)//2;env.update(r=r,betaP=scale-r)
    out=old.run(prefix(c)[0],env);out.update(K=c['K'],pell_tr1=2*r+1)
    assert all(x>0 for k,x in env.items() if k not in PARAMETERS)
    assert all(out[a]==out[b] for a,b in outer_comparisons()) and out['N']==raw['N']
    former=dict(env,F_N=raw['N']+1);del former['F_T']
    before=old.run(previous.prefix(c)[0],former);before.update(K=c['K'],pell_tr1=2*r+1)
    assert all(before[a]==before[b] for a,b in previous.outer_comparisons())
    for name in ('N','radix',prefix(c)[1],'index_rhs','packed_bound'):assert out[name]==before[name]
    conceptual=dict(out,S0=H-out['S1'],Gstar=out['Q']+A*H+H-out['S1'],
                    M0=out['L']-out['M1'],Ebar=c['c']*H-out['E'],Nbar=out['Nsum']-out['N'])
    assert all(0<=conceptual[f]<q and tag.boolean(conceptual[f]) for f in FIELDS)
    assert P==sum(conceptual[f]*q**i for i,f in enumerate(FIELDS))
    exponent=len(tag.trits(scale))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<scale and scale<r*r
    return dict(rows=t,leading=leading,T_zero=T==0,zero_terminal=tag.value(final)==0,parity=r%2)


def histories():
    cases=rows=unresolved=zeros=zero_final=0;parities=[0,0];branches=[0,0];branch_rows=[0,0]
    for beta in (1,2,3):
        for a in (2,3):
            for app in product((0,1),repeat=a):
                for length in range(beta,beta+3):
                    for initial in product((0,1),repeat=length):
                        w=tuple(initial);words=[];ss=[];ds=[]
                        for _ in range(20):
                            if len(w)<beta:break
                            words.append(w);ss.append(w[0]);ds.append(tag.value(w[:beta]))
                            w=w[beta:]+(app if w[0] else (0,))
                        if len(w)>=beta:unresolved+=1;continue
                        v=witness(beta,app,initial,words,ss,ds,w)
                        cases+=1;rows+=v['rows'];zeros+=v['T_zero'];zero_final+=v['zero_terminal']
                        parities[v['parity']]+=1;branches[v['leading']]+=1;branch_rows[v['leading']]+=v['rows']
    assert min(branches)>0 and zeros>0 and min(parities)>0
    return dict(canonical_histories=cases,rows=rows,leading_branch_histories=branches,leading_branch_rows=branch_rows,
                T_zero_histories=zeros,zero_terminal_histories=zero_final,kernel_index_parities=parities,
                cutoff_unclassified=unresolved,preserved_indices=cases,outer_comparisons_per_version=10,
                conceptual_masks=10,
                scope='Fresh105 and106 full outer tuples for actual computations stopping at their first halt, with unchanged original input parameters. P/r and all kernel coordinates are preserved; the generic converse supplies the enormous positive auxiliaries.')


def verify():
    return dict(status='PASS_GENERAL_SCALED_TAG_TRANSPORT_105',sources=[verify_source_branch(e) for e in (0,1)],
                identities=finite_identities(),negative_bootstrap=bootstrap_and_negative_pairs(),histories=histories(),
                proof='../1980/EXPLORATION_GENERAL_SCALED_TAG_TRANSPORT.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; construction and arithmetic frozen.',
                scope='Complete generic105 for every binary appendant of length at least two, with the original encoded-word parameters. Branch selection depends only on the fixed first appendant symbol, never on a runtime unknown.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print([{k:s[k] for k in ('leading','operations','multiplications','additions','positive_unknowns','equations')} for s in result['sources']])
    print(result['identities']);print(result['negative_bootstrap']);print(result['histories'])
