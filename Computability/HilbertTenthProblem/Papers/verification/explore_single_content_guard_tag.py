"""A complete nine-field104 tag certificate with only a guarded content word.

N itself is not masked. The first discrepant signed row is excluded by a
forbidden digit in the next guard, or its step already proves actual halting.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_general_scaled_tag_transport as previous

old=previous.old
tag=previous.tag
PARAMETERS=previous.PARAMETERS
POSITIVE=[x for x in previous.POSITIVE if x!='Nsum']
FIELDS=previous.FIELDS[:8]+['GN']


def constants(beta,app):
    c=tag.constants(beta,app);K=c['K']
    while c['C']<=max(K**3,K*3**len(app),2*K*c['U']+3):c['C']*=3
    c=previous.extended(c)
    c['guard_coefficient']=(c['C']-c['C']//K)//2
    assert 2*c['guard_coefficient']==c['C']-c['C']//K
    return c


def prefix(c):
    rows=[]
    for n,op,a,b in previous.prefix(c)[0]:
        if n in ('twice_content','content_length'):continue
        if n=='scale':rows.append((n,'*','q8','q'))
        elif n=='pack_mul0':rows.append(('guard_scale','*',c['guard_coefficient'],'A'))
        elif n=='pack_add0':
            rows.extend([('guard_base','*','guard_scale','H'),('pack_add0','+','guard_base','N')])
        else:rows.append((n,op,a,b))
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in old.kernel.SCHEDULE]


def outer_comparisons():
    return [p for p in previous.outer_comparisons() if p!=('content_length','L')]


def comparisons():
    return outer_comparisons()+[(old.rename(a),old.rename(b)) for a,b in old.kernel.EQUALITIES]


def conceptual(c,s):
    Q,S1,E=s['F_Q']-1,s['F_S1']-1,s['F_E']-1
    N=previous.content_coordinate(c,s);M1=2*Q+S1
    return dict(Gstar=Q+s['A']*s['H']+s['H']-S1,Q=Q,S0=s['H']-S1,S1=S1,
                M0=s['L']-M1,M1=M1,Ebar=c['c']*s['H']-E,E=E,
                GN=N+c['guard_coefficient']*s['A']*s['H'])


def sources(c,s):
    q,R,H,A=s['q'],s['R'],s['H'],s['A']
    T,E,Nf=s['F_T']-1,s['F_E']-1,s['F_Nfinal']-1
    N=previous.content_coordinate(c,s);M1=2*(s['F_Q']-1)+s['F_S1']-1
    raw=conceptual(c,s);P=sum(raw[f]*q**i for i,f in enumerate(FIELDS));D=c['Cbar']*A
    return [c['Khalf']*D-R,
            D*(T-E+c['Uthird']*M1)-(N-s['Ninit']+q*Nf),
            D*(s['L']+(c['B']-1)*M1)-(s['L']-s['Linit']+q*s['Lfinal']),
            s['Linit']+s['alphaI']-A,s['Lfinal']+s['alphaH']-c['K'],
            H*(R-1)-q+1,R*s['v']-q,2*s['r']+1-q**9-2*P,s['r']+s['betaP']-q**9]


def verify_source(leading):
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    Cbar,Kh,Ut,B,cc,j=sp.symbols('Cbar Khalf Uthird B c jguard')
    c=dict(Cbar=Cbar,Khalf=Kh,Uthird=Ut,B=B,c=cc,C=Kh*Cbar,K=3*Kh,
           U=3*Ut+leading,leading=leading,guard_coefficient=j)
    env=old.run(schedule(c),s);env['K']=c['K'];src=sources(c,s)
    sub={old.kernel.SYM[k]:s['q']**9 if k=='D0' else s[old.rename(k)] for k in old.kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in old.kernel.source_residuals()]
    src+=core;records=[]
    assert len(src)==len(comparisons())==20
    for i,((a,b),p) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i==17 else 0
        assert sp.expand(env[a]-env[b]-p-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(correction)))
    former=old.run(previous.prefix(c)[0],dict(s,Nsum=sp.Symbol('old_Nsum')))
    for n in ('N','M1','n_left','n_shift','l_left','l_shift','head_term','selector_term'):
        assert sp.expand(former[n]-env[n])==0,n
    assert all('Nsum' not in (n,a,b) for n,_,a,b in prefix(c)[0])
    dag=schedule(constants(2,(leading,1)))
    assert old.counts(dag)==dict(operations=104,multiplications=53,additions=51)
    assert len(POSITIVE)==len(set(POSITIVE))==33
    return dict(**old.counts(dag),leading=leading,positive_unknowns=33,equations=20,
                outer_equations=9,kernel_equations=11,fields=FIELDS,positive_coordinates=POSITIVE,
                parameters=PARAMETERS,dag=dag,sources=records,
                scope='Complete nine-field source; N is deliberately not a Boolean field. The stronger fixed C is compiled, not supplied.')


def finite_bounds():
    cases=0
    for beta in (1,2,3,4):
        K=3**beta;k=K//3
        for B in (3,9,27):
            U=(3*B-1)//2;C=3**(3*beta+2)
            while C<=max(K**3,3*K*B,2*K*U+3):C*=3
            for A,H in product((K+1,3*K,9*K),(1,2,7)):
                R=C*A;q=(R-1)*H+1
                assert q>=R and R>K*K
                assert Fraction(k*K*q,R-k)<Fraction(q,2)
                assert Fraction(k*K*q,R*(B-1))<Fraction(q,6)
                jg=Fraction((R-R//K)*H,2)
                assert jg>=Fraction(q-1,3) and jg-Fraction(q,6)>0
                assert Fraction(A+1,R-1)<Fraction(1,3)
                assert U*Fraction(k*K*q,R*(B-1))<Fraction(3*q,4)
                assert Fraction(5*q,12)+Fraction(1,6)<Fraction(q,2)
                D0=q**9;low=Fraction(D0-1,2)
                assert low>27 and low*low>D0
                cases+=1
    return dict(prepower_rational_cases=cases,
                scope='Exact necessary scalar inequalities with arbitrary positive H and nonpower radices; no digit assumption is used.')


def signed_chunk_gate():
    cases=negative=typed=0
    for q in (3,9,27,81):
        J=(q-1)//2
        for w in range(-J,q):
            for carryless_lower in (0,1,q-1):
                block=w%q
                if w<0:
                    assert block>J and not tag.boolean(block);negative+=1
                if tag.boolean(block):
                    assert w>=0 and tag.boolean(w);typed+=1
                assert (carryless_lower+q*w)//q%q==block
                cases+=1
    return dict(signed_chunk_cases=cases,negative_chunk_rejections=negative,Boolean_nonnegative_cases=typed,
                scope='Sequential q-block recovery with zero incoming carry; higher blocks may be signed.')


def borrow_gate():
    cases=bad_read=forbidden=monotone=0
    for beta in (1,2,3):
        K=3**beta;c=(K-1)//2;z=3**(beta+1);b=K*z
        for v in range(min(z,100)):
            if not tag.boolean(v):continue
            p=v%K
            for s in range(c+1):
                n=v-s*b;G=c*b+n
                if not tag.boolean(G):continue
                assert tag.boolean(c-s) and tag.boolean(s)
                d=p+s
                if not tag.boolean(d):continue
                assert 0<=d<=c and d%3>=p%3
                cases+=1;bad_read+=d!=p
                for ell,a in product((beta,beta+1),(2,3,5)):
                    encoded=ell-beta+(a if d%3 else 1)
                    actual=ell-beta+(a if p%3 else 1)
                    assert actual<=encoded;monotone+=1
                if s:
                    for vp,next_carry in product((0,1,z//3,z-1),(-2,0,1,c,c+1)):
                        nnext=vp-s*z-next_carry*b;Gnext=c*b+nnext
                        residue=Gnext%b
                        assert residue==(K-s)*z+vp
                        assert residue//z==K-s>c
                        assert not tag.boolean(residue)
                        assert not (Gnext>=0 and tag.boolean(Gnext));forbidden+=1
    assert bad_read and forbidden
    return dict(admitted_local_reads=cases,altered_prefix_reads=bad_read,
                next_guard_rejections=forbidden,terminal_monotonicity_cases=monotone,
                scope='All small admitted initial guard/prefix reads, including wrong prefixes. Arbitrary signed next carries cannot remove the forbidden beta-trit block. These are local implications, not full source tuples.')


def witness(beta,app,initial,words,ss,ds,final):
    c=constants(beta,app)
    A=3**(1+max(map(len,[initial]+words)));R=c['C']*A
    t=len(words);q=R**t;H=(q-1)//(R-1)
    vals=dict.fromkeys(('Q','S1','M0','M1','E','N'),0)
    for i,(w,sel,d) in enumerate(zip(words,ss,ds)):
        wt=R**i;li=3**len(w);n=tag.value(w)
        vals['Q']+=sel*(li-1)//2*wt;vals['S1']+=sel*wt
        vals['M'+str(sel)]+=li*wt;vals['E']+=(d-sel)//3*wt;vals['N']+=n*wt
    T=(vals['N']-vals['S1'])//3 if c['leading']==0 else (vals['N']+2*vals['Q'])//3
    assert previous.content_coordinate(c,dict(F_T=T+1,F_Q=vals['Q']+1,F_S1=vals['S1']+1))==vals['N']
    s=dict(F_Q=vals['Q']+1,F_S1=vals['S1']+1,F_T=T+1,F_E=vals['E']+1,
           F_Nfinal=tag.value(final)+1,A=A,R=R,q=q,H=H,L=vals['M0']+vals['M1'],
           Lfinal=3**len(final),Ninit=tag.value(initial),Linit=3**len(initial),
           alphaI=A-3**len(initial),alphaH=c['K']-3**len(final),v=q//R)
    first=old.run(prefix(c)[0][:-3],s);P=first[prefix(c)[1]];D0=q**9;r=P+(D0-1)//2
    s.update(r=r,betaP=D0-r)
    env=old.run(prefix(c)[0],s);env.update(K=c['K'],pell_tr1=2*r+1)
    assert all(env[a]==env[b] for a,b in outer_comparisons())
    assert all(v>0 for n,v in s.items() if n not in PARAMETERS)
    raw=conceptual(c,s)
    assert all(0<=v<q and tag.boolean(v) for v in raw.values())
    assert P==sum(raw[f]*q**i for i,f in enumerate(FIELDS))
    exponent=len(tag.trits(D0))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<D0 and D0<r*r
    assert raw['GN']==vals['N']+c['guard_coefficient']*A*H
    assert raw['Gstar']%3==1
    return dict(rows=t,leading=c['leading'],parity=r%2,T_zero=T==0,zero_final=tag.value(final)==0,
                zero_prefix=vals['E']==0)


def histories():
    count=rows=cutoff=zeroT=zero_final=zero_prefix=0;branches=[0,0];parities=[0,0]
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
                        if len(w)>=beta:cutoff+=1;continue
                        v=witness(beta,app,initial,words,ss,ds,w)
                        count+=1;rows+=v['rows'];branches[v['leading']]+=1;parities[v['parity']]+=1
                        zeroT+=v['T_zero'];zero_final+=v['zero_final'];zero_prefix+=v['zero_prefix']
    assert min(branches)>0 and min(parities)>0 and zeroT and zero_final
    return dict(actual_halting_histories=count,source_rows=rows,leading_branch_histories=branches,
                kernel_index_parities=parities,T_zero_histories=zeroT,zero_final_histories=zero_final,
                zero_prefix_histories=zero_prefix,cutoff_unclassified=cutoff,
                outer_comparisons_per_tuple=9,masked_words_per_tuple=9,
                scope='Actual computations stopped at first halt. Every new outer comparison, positive coordinate, nine masks and exact index valuation is checked. The generic44 theorem supplies fresh positive auxiliaries; none are copied from105 or materialized.')


def verify():
    return dict(status='PASS_SINGLE_CONTENT_GUARD_TAG_104',sources=[verify_source(e) for e in (0,1)],
                bounds=finite_bounds(),signed_chunks=signed_chunk_gate(),borrow=borrow_gate(),histories=histories(),
                proof='../1980/EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; proof and arithmetic frozen.',
                scope='Complete104 for the original encoded binary input and every fixed binary appendant of length at least two. The genuine radix-divisibility equation is retained. No unmasked content word or endpoint is silently typed; no universal raw-input bound is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print([{k:r[k] for k in ('leading','operations','multiplications','additions','positive_unknowns','equations')} for r in result['sources']])
    print({k:v for k,v in result.items() if k not in ('sources','proof','review','scope')})
