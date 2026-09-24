"""Reuse the computed selected marker instead of adapting a duplicate input."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_implicit_selector_complement_tag as previous

old=previous.old
tag=previous.tag
RAW=[x for x in previous.RAW if x!='M1']
FIELDS=previous.FIELDS
POSITIVE=[x for x in previous.POSITIVE if x!='F_M1']
PARAMETERS=previous.PARAMETERS


def prefix(c):
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name=='M1':continue
        rows.append(('M1' if name=='marker1' else name,op,a,b))
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in old.kernel.SCHEDULE]


def outer_comparisons():
    return [p for p in previous.outer_comparisons() if p!=('marker1','M1')]


def comparisons():
    return outer_comparisons()+[(old.rename(a),old.rename(b)) for a,b in old.kernel.EQUALITIES]


def verify_source():
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    c=dict(zip('C K Khalf B U c'.split(),sp.symbols('C K Khalf B U c')))
    former=dict(s,F_M1=2*s['F_Q']+s['F_S1']-2)
    src=previous.sources(c,former)
    assert sp.expand(src[1])==0
    src=src[:1]+src[2:]
    env=old.run(schedule(c),s);env['K']=c['K']
    sub={old.kernel.SYM[k]:(s['q']**10 if k=='D0' else s[old.rename(k)]) for k in old.kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in old.kernel.source_residuals()]
    src+=core;records=[]
    for i,((a,b),p) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i==20 else 0
        assert sp.expand(env[a]-env[b]-p-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(correction)))
    before=old.run(previous.schedule(c),former)
    assert sp.expand(before['marker1']-before['M1'])==0
    for x in ['M1',prefix(c)[1],'index_rhs','pell_tr1']:
        assert sp.expand(before[x]-env[x])==0
    dag=schedule(tag.constants(2,(1,0,0)))
    assert old.counts(dag)==dict(operations=112,multiplications=55,additions=57)
    assert len(POSITIVE)==len(set(POSITIVE))==36 and len(src)==23
    return dict(**old.counts(dag),positive_unknowns=36,equations=23,outer_equations=12,
                kernel_equations=11,positive_coordinates=POSITIVE,fields=FIELDS,
                parameters=PARAMETERS,dag=dag,sources=records,
                positive_inverse='F_M1=2F_Q+F_S1-2>=1',
                same_packing_index_and_kernel_witnesses=True)


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
    scale=q**10;r=P+(scale-1)//2;env.update(r=r,betaP=scale-r)
    out=old.run(prefix(c)[0],env);out.update(K=c['K'],pell_tr1=2*r+1)
    assert all(out[a]==out[b] for a,b in outer_comparisons())
    assert all(x>0 for key,x in env.items() if key not in PARAMETERS)
    assert out['M1']==raw['M1']==2*out['Q']+out['S1']
    assert all(0<=out[f]<q and tag.boolean(out[f]) for f in FIELDS)
    exponent=len(tag.trits(scale))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<scale and scale<r*r
    restored=dict(env,F_M1=out['M1']+1)
    before=old.run(previous.prefix(c)[0],restored);before.update(K=c['K'],pell_tr1=2*r+1)
    assert all(before[a]==before[b] for a,b in previous.outer_comparisons())
    assert before[previous.prefix(c)[1]]==P and before['index_rhs']==out['index_rhs']
    return dict(rows=t,parity=r%2,M1_zero=out['M1']==0)


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
                        cases+=1;rows+=z['rows'];zeros+=z['M1_zero'];parities[z['parity']]+=1
    post=witness(2,(1,0,0),(0,0),[(0,0),(0,),()],[0,0,1],[0,0,1],(0,))
    assert zeros>0 and min(parities)>0
    return dict(canonical_histories=cases,rows=rows,cutoff_unclassified=unresolved,
                kernel_index_parities=parities,zero_selected_marker_histories=zeros,
                post_halt_example=post,new_outer_comparisons=12,restored_outer_comparisons=13,
                typed_fields=10,preserved_indices=cases,
                scope='Fresh actual112 outer schedules and the restored113 schedules, all masks and exact native valuations. Huge Pell auxiliaries are justified by exact preservation and the existing converse, not materialized.')


def verify():
    return dict(status='PASS_DERIVED_SELECTED_MARKER_TAG',source=verify_source(),histories=histories(),
                review_status='Author plus independent root and binary complete proof/source reviews and fresh runs passed without findings. Mathematical construction and arithmetic frozen.',
                proof='../1980/EXPLORATION_DERIVED_SELECTED_MARKER_TAG.md',
                scope='Exact positive-coordinate bijection for the encoded binary word tag certificate. No new mask assumptions, ordinary raw-input conversion or universal-bound claim.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:result['source'][k] for k in ['operations','multiplications','additions','positive_unknowns','equations']})
    print(result['histories'])
