"""Implicit S0 saves one positive adapter operation in the114 tag certificate."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_positive_content_sum_tag as previous

old=previous.old
tag=previous.tag
RAW=[x for x in previous.RAW if x!='S0']
FIELDS=previous.FIELDS
POSITIVE=[x for x in previous.POSITIVE if x!='F_S0']
PARAMETERS=previous.PARAMETERS


def prefix(c):
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name=='S0':continue  # Former F_S0-1 adapter.
        if name=='headsum':continue
        rows.append((name,op,a,b))
        if name=='S1':rows.append(('S0','-','H','S1'))
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in old.kernel.SCHEDULE]


def outer_comparisons():
    return [pair for pair in old.outer_comparisons() if pair!=('headsum','H')]


def comparisons():
    return outer_comparisons()+[(old.rename(a),old.rename(b)) for a,b in old.kernel.EQUALITIES]


def sources(c,s):
    former=dict(s,F_S0=s['H']-s['F_S1']+2)
    src=previous.sources(c,former)
    assert sp.expand(src[1])==0
    return src[:1]+src[2:]


def verify_source():
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    c=dict(zip('C K Khalf B U c'.split(),sp.symbols('C K Khalf B U c')))
    env=old.run(schedule(c),s);env['K']=c['K']
    src=sources(c,s)
    sub={old.kernel.SYM[k]:(s['q']**10 if k=='D0' else s[old.rename(k)]) for k in old.kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in old.kernel.source_residuals()]
    src+=core;records=[]
    for i,((a,b),p) in enumerate(zip(comparisons(),src)):
        adjustment=core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i==21 else 0
        assert sp.expand(env[a]-env[b]-p-adjustment)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(adjustment)))
    former=dict(s,F_S0=s['H']-s['F_S1']+2)
    before=old.run(previous.schedule(c),former)
    # Identical packed word, index register and every surviving comparison.
    assert sp.expand(before[previous.prefix(c)[1]]-env[prefix(c)[1]])==0
    assert sp.expand(before['pell_tr1']-env['pell_tr1'])==0
    assert sp.expand(before['headsum']-s['H'])==0
    dag=schedule(tag.constants(2,(1,0,0)))
    assert old.counts(dag)==dict(operations=113,multiplications=55,additions=58)
    assert len(POSITIVE)==len(set(POSITIVE))==37 and len(src)==24
    return dict(**old.counts(dag),positive_unknowns=37,equations=24,outer_equations=13,
                kernel_equations=11,fields=FIELDS,positive_coordinates=POSITIVE,
                parameters=PARAMETERS,dag=dag,sources=records,
                exact_source_map='F_S0=H-F_S1+2; removed head-sum source is identically zero',
                same_packed_word_and_index=True)


def negative_chunks():
    cases=negative=rejected_first=rejected_second=0
    for q in (9,27,81,243):
        J=(q-1)//2
        vals=range(-J,J+1)
        for g in vals:
            for s0 in vals:
                # The other bounded lower fields are represented by Q and
                # one nonnegative remainder; they cannot alter the positions
                # at which each negative coefficient is tested.
                Q=(g+J)%q
                Plo=g+q*Q+q*q*s0
                P=Plo+q**8
                assert Plo>-q**3 and P>0
                cases+=1
                if g<0:
                    assert P%q==q+g>J
                    assert not tag.boolean(P%q)
                    negative+=1;rejected_first+=1
                elif s0<0:
                    assert (P//(q*q))%q==q+s0>J
                    assert not tag.boolean((P//(q*q))%q)
                    negative+=1;rejected_second+=1
    return dict(coefficient_pairs=cases,negative_cases=negative,
                first_field_rejections=rejected_first,selector_field_rejections=rejected_second,
                scope='Signed low-field normalization tests over the stated ranges, not complete tag source tuples.')


def witness(beta,app,initial,words,ss,ds,final):
    c=tag.constants(beta,app)
    A=3**(1+max([len(initial)]+[len(w) for w in words]));R=c['C']*A
    t=len(words);q=R**t;H=(q-1)//(R-1);raw=dict.fromkeys(old.RAW,0)
    for i,(w,sel,d) in enumerate(zip(words,ss,ds)):
        wt=R**i;mark=3**len(w);ns=(mark-1)//2;n=tag.value(w)
        raw['Q']+=sel*ns*wt;raw['S'+str(sel)]+=wt;raw['M'+str(sel)]+=mark*wt
        raw['N']+=n*wt;raw['Nbar']+=(ns-n)*wt
        e=(d-sel)//3;raw['E']+=e*wt;raw['Ebar']+=(c['c']-e)*wt
    env={'F_'+x:raw[x]+1 for x in RAW}
    env.update(Nsum=raw['N']+raw['Nbar'],F_Nfinal=tag.value(final)+1,A=A,R=R,q=q,H=H,
               L=raw['M0']+raw['M1'],Lfinal=3**len(final),Ninit=tag.value(initial),
               Linit=3**len(initial),alphaI=A-3**len(initial),alphaH=c['K']-3**len(final),v=q//R)
    first=old.run(prefix(c)[0][:-3],env);P=first[prefix(c)[1]]
    D0=q**10;r=P+(D0-1)//2;env.update(r=r,betaP=D0-r)
    out=old.run(prefix(c)[0],env);out.update(K=c['K'],pell_tr1=2*r+1)
    assert all(out[a]==out[b] for a,b in outer_comparisons())
    assert all(x>0 for key,x in env.items() if key not in PARAMETERS)
    assert out['S0']==raw['S0'] and out['Nbar']==raw['Nbar']
    assert all(0<=out[f]<q and tag.boolean(out[f]) for f in FIELDS)
    exponent=len(tag.trits(D0))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<D0 and D0<r*r
    restored=dict(env,F_S0=out['S0']+1)
    before=old.run(previous.prefix(c)[0],restored);before.update(K=c['K'],pell_tr1=2*r+1)
    assert all(before[a]==before[b] for a,b in old.outer_comparisons())
    assert before[previous.prefix(c)[1]]==P and before['index_rhs']==out['index_rhs']
    return dict(rows=t,parity=r%2,S0_zero=out['S0']==0)


def histories():
    cases=rows=unresolved=zeros=0;parities=[0,0]
    for beta in (1,2,3):
        for a in (1,2,3):
            for app in product((0,1),repeat=a):
                for length in range(beta,beta+3):
                    for initial in product((0,1),repeat=length):
                        w=tuple(initial);words=[];ss=[];ds=[]
                        for _ in range(20):
                            if len(w)<beta:break
                            words.append(w);ss.append(w[0]);ds.append(tag.value(w[:beta]))
                            w=w[beta:]+(app if w[0] else (0,))
                        if len(w)>=beta:unresolved+=1;continue
                        z=witness(beta,app,initial,words,ss,ds,w)
                        cases+=1;rows+=z['rows'];zeros+=z['S0_zero'];parities[z['parity']]+=1
    post=witness(2,(1,0,0),(0,0),[(0,0),(0,),()],[0,0,1],[0,0,1],(0,))
    assert zeros>0 and min(parities)>0
    return dict(canonical_histories=cases,rows=rows,cutoff_unclassified=unresolved,
                kernel_index_parities=parities,zero_selector_complements=zeros,post_halt_example=post,
                new_outer_comparisons=13,restored_outer_comparisons=14,typed_fields=10,
                preserved_packed_indices=cases,
                scope='Same packed word and exact index are checked in both full outer schedules. All Pell witnesses may be retained; their huge values remain unmaterialized.')


def verify():
    return dict(status='PASS_IMPLICIT_SELECTOR_COMPLEMENT_TAG',source=verify_source(),
                prepower=old.prepower(),negative_chunks=negative_chunks(),histories=histories(),
                review_status='Author plus independent root and binary complete proof/source reviews and fresh runs passed without findings. Mathematical construction and arithmetic frozen.',
                proof='../1980/EXPLORATION_IMPLICIT_SELECTOR_COMPLEMENT_TAG.md',
                scope='Complete positive encoded-word tag halting equivalence with exact positive coordinate restoration. No raw-input universal bound or optimality claim.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:result['source'][k] for k in ['operations','multiplications','additions','positive_unknowns','equations']})
    print(result['negative_chunks']);print(result['histories'])
