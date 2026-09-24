"""Recover M0=L-M1 for binary appendants of length at least two."""
from itertools import product
from pathlib import Path
from fractions import Fraction
import json
import sympy as sp
import explore_implicit_prefix_complement_tag as previous

old=previous.old
tag=previous.tag
RAW=[x for x in previous.RAW if x!='M0']
FIELDS=previous.FIELDS
POSITIVE=[x for x in previous.POSITIVE if x!='F_M0']
PARAMETERS=previous.PARAMETERS


def prefix(c):
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name in ('M0','lengthsum'):continue
        rows.append((name,op,a,b))
        if name=='M1':rows.append(('M0','-','L','M1'))
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in old.kernel.SCHEDULE]


def outer_comparisons():
    return [p for p in previous.outer_comparisons() if p!=('lengthsum','L')]


def comparisons():
    return outer_comparisons()+[(old.rename(a),old.rename(b)) for a,b in old.kernel.EQUALITIES]


def sources(c,s):
    former=dict(s,F_M0=s['L']-2*s['F_Q']-s['F_S1']+4)
    src=previous.sources(c,former)
    assert sp.expand(src[1])==0
    return src[:1]+src[2:]


def verify_source():
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    c=dict(zip('C K Khalf B U c'.split(),sp.symbols('C K Khalf B U c')))
    env=old.run(schedule(c),s);env['K']=c['K'];src=sources(c,s)
    sub={old.kernel.SYM[k]:(s['q']**10 if k=='D0' else s[old.rename(k)]) for k in old.kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in old.kernel.source_residuals()]
    src+=core;records=[]
    assert len(src)==len(comparisons())==21
    for i,((a,b),p) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i==18 else 0
        assert sp.expand(env[a]-env[b]-p-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(correction)))
    former=dict(s,F_M0=s['L']-2*s['F_Q']-s['F_S1']+4)
    before=old.run(previous.prefix(c)[0],former)
    assert sp.expand(before[previous.prefix(c)[1]]-env[prefix(c)[1]])==0
    assert sp.expand(before['index_rhs']-env['index_rhs'])==0
    dag=schedule(tag.constants(2,(1,0)))
    assert old.counts(dag)==dict(operations=110,multiplications=55,additions=55)
    assert len(POSITIVE)==len(set(POSITIVE))==34
    return dict(**old.counts(dag),positive_unknowns=34,equations=21,outer_equations=10,
                kernel_equations=11,positive_coordinates=POSITIVE,fields=FIELDS,
                parameters=PARAMETERS,dag=dag,sources=records,
                former_coordinate='F_M0=L-2F_Q-F_S1+4, recovered positive after decoding',
                changed_packing_order=False,
                contract='Appendants have length at least two; B>=3. No source guarantee is asserted here for B=1.')


def marker_pairs():
    cases=negative=accepted=0;rational=0
    for K in (3,9,27):
        for B in (3,9,27):
            for R in range(K*K+1,K*K+6):
                assert Fraction(K*(2*K+1),6*R*(B-1))<Fraction(7,36)<Fraction(1,2)
                rational+=1
    for q in (3,9,27,81,243):
        J=(q-1)//2
        for L in range(1,J+1):
            for M1 in range(J+1):
                M0=L-M1;pair=M0+q*M1
                assert pair==L+(q-1)*M1>0 and -Fraction(q,2)<M0<Fraction(q,2)
                if M0<0:
                    negative+=1
                    assert pair%q==q+M0>J and not tag.boolean(pair)
                if tag.boolean(pair):
                    accepted+=1
                    assert M0>=0 and tag.boolean(M0) and tag.boolean(M1)
                cases+=1
    return dict(marker_pairs=cases,negative_markers_rejected=negative,
                Boolean_pairs_accepted=accepted,rational_M1_bounds=rational,
                scope='Normalization after the proved scalar bounds; pair ranges enlarge the actual source interface. They are not full tag sources.')


def witness(beta,app,initial,words,ss,ds,final):
    assert len(app)>=2
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
    assert out['M0']==raw['M0'] and out['Ebar']==raw['Ebar'] and out['Nbar']==raw['Nbar']
    assert all(0<=out[f]<q and tag.boolean(out[f]) for f in FIELDS)
    assert 2*out['M1']<q and 2*out['N']<q and 2*out['E']<q
    exponent=len(tag.trits(scale))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<scale and scale<r*r
    restored=dict(env,F_M0=out['M0']+1)
    before=old.run(previous.prefix(c)[0],restored);before.update(K=c['K'],pell_tr1=2*r+1)
    assert all(before[a]==before[b] for a,b in previous.outer_comparisons())
    assert before[previous.prefix(c)[1]]==P and before['index_rhs']==out['index_rhs']
    return dict(rows=t,parity=r%2,M0_zero=out['M0']==0,index_preserved=True)


def histories():
    cases=rows=unresolved=zeros=0;parities=[0,0]
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
                        z=witness(beta,app,initial,words,ss,ds,w)
                        cases+=1;rows+=z['rows'];zeros+=z['M0_zero'];parities[z['parity']]+=1
    post=witness(2,(1,0,0),(0,0),[(0,0),(0,),()],[0,0,1],[0,0,1],(0,))
    assert zeros>0 and min(parities)>0
    return dict(canonical_histories=cases,rows=rows,cutoff_unclassified=unresolved,
                kernel_index_parities=parities,zero_unselected_markers=zeros,
                preserved_indices=cases,post_halt_example=post,new_outer_comparisons=10,
                restored_outer_comparisons=11,typed_fields=10,
                scope='Both actual prefixes, all outer equations and valuations are freshly evaluated. All existing Pell witnesses are preserved by the exact positive-coordinate extension.')


def single_symbol_semantics():
    halts=constant=0
    for beta in (1,2,3,4):
        for app in ((0,),(1,)):
            for length in range(beta,beta+3):
                for initial in product((0,1),repeat=length):
                    w=initial;steps=0
                    if beta==1:
                        for _ in range(10):
                            w=w[beta:]+(app if w[0] else (0,))
                            assert len(w)==length
                        constant+=1
                    else:
                        while len(w)>=beta:
                            previous_length=len(w)
                            w=w[beta:]+(app if w[0] else (0,));steps+=1
                            assert len(w)==previous_length-(beta-1)
                        assert steps==(length-beta)//(beta-1)+1
                        halts+=1
    return dict(decreasing_length_halts=halts,constant_length_nonhalts=constant,
                scope='A separate elementary semantic classification for one-symbol appendants, not a claimed source theorem for the110 schedule at B=1.')


def verify():
    return dict(status='PASS_IMPLICIT_UNSELECTED_MARKER_TAG',source=verify_source(),
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; construction and arithmetic frozen.',
                marker_pairs=marker_pairs(),histories=histories(),single_symbol=single_symbol_semantics(),
                proof='../1980/EXPLORATION_IMPLICIT_UNSELECTED_MARKER_TAG.md',
                scope='Complete positive encoded-word halting equivalence for binary appendants of length at least two. No raw-input universal bound or optimality claim.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:result['source'][k] for k in ['operations','multiplications','additions','positive_unknowns','equations']})
    print(result['marker_pairs']);print(result['histories']);print(result['single_symbol'])
