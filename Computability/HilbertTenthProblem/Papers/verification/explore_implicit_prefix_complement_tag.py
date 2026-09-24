"""Recover the prefix complement after bounding N and then E."""
from itertools import product
from pathlib import Path
from fractions import Fraction
import json
import sympy as sp
import explore_derived_selected_marker_tag as previous

old=previous.old
tag=previous.tag
RAW=[x for x in previous.RAW if x!='Ebar']
FIELDS='Gstar Q S0 S1 M0 M1 Ebar E Nbar N'.split()
POSITIVE=[x for x in previous.POSITIVE if x!='F_Ebar']
PARAMETERS=previous.PARAMETERS


def prefix(c):
    rows=[];last=FIELDS[-1]
    for name,op,a,b in previous.prefix(c)[0]:
        if name in ('Ebar','prefix_sum') or name.startswith('pack_'):continue
        if name=='twiceP':
            for i,f in enumerate(reversed(FIELDS[:-1])):
                rows += [(f'pack_mul{i}','*','q',last),(f'pack_add{i}','+',f,f'pack_mul{i}')]
                last=f'pack_add{i}'
        rows.append((name,op,a,b))
        if name=='prefix_scale':rows.append(('Ebar','-','prefix_scale','E'))
    return rows,last


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in old.kernel.SCHEDULE]


def outer_comparisons():
    return [p for p in previous.outer_comparisons() if p!=('prefix_sum','prefix_scale')]


def comparisons():
    return outer_comparisons()+[(old.rename(a),old.rename(b)) for a,b in old.kernel.EQUALITIES]


def sources(c,s):
    former=dict(s,F_Ebar=c['c']*s['H']-s['F_E']+2,F_M1=2*s['F_Q']+s['F_S1']-2)
    src=previous.previous.sources(c,former)
    assert sp.expand(src[1])==0
    src=src[:1]+src[2:]  # The112 output reuse.
    assert sp.expand(src[3])==0
    src=src[:3]+src[4:]
    z=dict(s)
    for x in RAW+['Nfinal']:z[x]=s['F_'+x]-1
    z.update(S0=z['H']-z['S1'],M1=2*z['Q']+z['S1'],Nbar=z['Nsum']-z['N'],
             Ebar=c['c']*z['H']-z['E'])
    z['Gstar']=z['Q']+z['A']*z['H']+z['S0']
    P=sum(z[f]*z['q']**i for i,f in enumerate(FIELDS))
    src[9]=2*z['r']+1-z['q']**10-2*P
    return [sp.expand(p) for p in src]


def verify_source():
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    c=dict(zip('C K Khalf B U c'.split(),sp.symbols('C K Khalf B U c')))
    env=old.run(schedule(c),s);env['K']=c['K'];src=sources(c,s)
    sub={old.kernel.SYM[k]:(s['q']**10 if k=='D0' else s[old.rename(k)]) for k in old.kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in old.kernel.source_residuals()]
    src+=core;records=[]
    for i,((a,b),p) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i==19 else 0
        assert sp.expand(env[a]-env[b]-p-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(correction)))
    dag=schedule(tag.constants(2,(1,0,0)))
    assert old.counts(dag)==dict(operations=111,multiplications=55,additions=56)
    assert len(POSITIVE)==len(set(POSITIVE))==35 and len(src)==22
    return dict(**old.counts(dag),positive_unknowns=35,equations=22,outer_equations=11,
                kernel_equations=11,positive_coordinates=POSITIVE,fields=FIELDS,
                parameters=PARAMETERS,dag=dag,sources=records,
                former_coordinate='F_Ebar=cH-F_E+2; its positivity is recovered after decoding',
                changed_packing_order=True)


def prefix_pairs():
    cases=negative=accepted=0;bound_cases=0
    for q in (3,9,27,81,243):
        J=(q-1)//2
        assert Fraction(13*q,36)+Fraction(1,6)<Fraction(q,2)
        assert -J*(1+q*q)>-q**3 and q**8-J*(1+q*q)>0
        bound_cases+=1
        for base in range(q):
            for E in range(J+1):
                Eb=base-E;packed=Eb+q*E
                assert packed==base+(q-1)*E>=0
                if Eb<0:
                    negative+=1
                    assert -Fraction(q,2)<Eb and packed%q==q+Eb>J
                    assert not tag.boolean(packed)
                if tag.boolean(packed):
                    accepted+=1
                    assert Eb>=0 and tag.boolean(Eb) and tag.boolean(E)
                cases+=1
    assert negative>0 and accepted>0
    return dict(prefix_pairs=cases,negative_complements_rejected=negative,
                Boolean_pairs_accepted=accepted,strict_rational_E_bound_cases=bound_cases,
                scope='Prefix-pair normalization after the proved E bound; arbitrary bases0..q-1 give a stronger finite range than the actual fixed cH. These are not full source tuples.')


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
    assert out['Ebar']==raw['Ebar'] and out['Nbar']==raw['Nbar']
    assert all(0<=out[f]<q and tag.boolean(out[f]) for f in FIELDS)
    assert 2*out['N']<q and 2*out['E']<q
    exponent=len(tag.trits(scale))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<scale and scale<r*r
    restored=dict(env,F_Ebar=out['Ebar']+1)
    before0=old.run(previous.prefix(c)[0][:-3],restored);Pold=before0[previous.prefix(c)[1]]
    rold=Pold+(scale-1)//2;restored.update(r=rold,betaP=scale-rold)
    before=old.run(previous.prefix(c)[0],restored);before.update(K=c['K'],pell_tr1=2*rold+1)
    assert all(before[a]==before[b] for a,b in previous.outer_comparisons())
    assert old.unit.valuation(rold)==exponent
    return dict(rows=t,parity=r%2,Ebar_zero=out['Ebar']==0,index_changed=r!=rold)


def histories():
    cases=rows=unresolved=zeros=changed=0;parities=[0,0]
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
                        cases+=1;rows+=z['rows'];zeros+=z['Ebar_zero'];changed+=z['index_changed']
                        parities[z['parity']]+=1
    post=witness(2,(1,0,0),(0,0),[(0,0),(0,),()],[0,0,1],[0,0,1],(0,))
    assert zeros>0 and changed>0 and min(parities)>0
    return dict(canonical_histories=cases,rows=rows,cutoff_unclassified=unresolved,
                kernel_index_parities=parities,zero_prefix_complements=zeros,changed_indices=changed,
                post_halt_example=post,new_outer_comparisons=11,restored_outer_comparisons=12,typed_fields=10,
                scope='Both actual packing orders, full outer equations and exact valuations are freshly constructed. Positive Pell auxiliaries for the new index are supplied by the reviewed generic theorem, not materialized.')


def verify():
    return dict(status='PASS_IMPLICIT_PREFIX_COMPLEMENT_TAG',source=verify_source(),
                review='Author and independent root, binary and algebra complete proof/source reviews and fresh runs PASS; construction and arithmetic frozen.',
                prefix_pairs=prefix_pairs(),histories=histories(),
                proof='../1980/EXPLORATION_IMPLICIT_PREFIX_COMPLEMENT_TAG.md',
                scope='Complete positive encoded-word halting equivalence for arbitrary nonempty binary appendant. No raw-input universal bound or optimality claim.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:result['source'][k] for k in ['operations','multiplications','additions','positive_unknowns','equations']})
    print(result['prefix_pairs']);print(result['histories'])
