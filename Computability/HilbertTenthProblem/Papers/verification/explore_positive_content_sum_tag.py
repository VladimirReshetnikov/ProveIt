"""Positive content-sum coordinates save one operation in the encoded tag proof."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_single_projector_tag_packing as old

tag=old.tag
RAW=[x for x in old.RAW if x!='Nbar']
FIELDS='Gstar Q S0 S1 M0 M1 E Ebar Nbar N'.split()
POSITIVE=['Nsum' if x=='F_Nbar' else x for x in old.POSITIVE]
PARAMETERS=old.PARAMETERS


def prefix(c):
    rows=[(x,'-','F_'+x,1) for x in RAW+['Nfinal']]
    rows.append(('Nbar','-','Nsum','N'))
    for name,op,a,b in old.reduced.schedule(c):
        if name=='content_sum':continue
        rows.append((name,op,'Nsum' if a=='content_sum' else a,
                     'Nsum' if b=='content_sum' else b))
    rows += [('Gstar','+','G','S0'),('qm1','-','q',1),('Rm1','-','R',1),
             ('head_product','*','H','Rm1'),('radix_product','*','R','v'),
             ('q2','*','q','q'),('q4','*','q2','q2'),('q8','*','q4','q4'),
             ('scale','*','q8','q2')]
    last=FIELDS[-1]
    for i,f in enumerate(reversed(FIELDS[:-1])):
        rows += [(f'pack_mul{i}','*','q',last),(f'pack_add{i}','+',f,f'pack_mul{i}')]
        last=f'pack_add{i}'
    rows += [('twiceP','+',last,last),('index_rhs','+','scale','twiceP'),
             ('packed_bound','+','r','betaP')]
    return rows,last


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in old.kernel.SCHEDULE]


def sources(c,s):
    former=dict(s,F_Nbar=s['Nsum']-s['F_N']+2)
    source=old.sources(c,former)
    z=dict(s,Nbar=s['Nsum']-(s['F_N']-1))
    for x in RAW+['Nfinal']:z[x]=s['F_'+x]-1
    z['Gstar']=z['Q']+z['A']*z['H']+z['S0']
    P=sum(z[f]*s['q']**i for i,f in enumerate(FIELDS))
    source[12]=2*s['r']+1-s['q']**10-2*P
    return [sp.expand(p) for p in source]


def verify_source():
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    c=dict(zip('C K Khalf B U c'.split(),sp.symbols('C K Khalf B U c')))
    env=old.run(schedule(c),s);env['K']=c['K']
    src=sources(c,s)
    sub={old.kernel.SYM[k]:(s['q']**10 if k=='D0' else s[old.rename(k)])
         for k in old.kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in old.kernel.source_residuals()]
    src+=core;records=[]
    for i,((a,b),p) in enumerate(zip(old.comparisons(),src)):
        correction=core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i==22 else 0
        assert sp.expand(env[a]-env[b]-p-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(correction)))
    # Every nonpacking outer source is the literal115 source under its unique
    # formal coordinate substitution; positivity of that inverse is proved.
    former=dict(s,F_Nbar=s['Nsum']-s['F_N']+2)
    for i,(before,after) in enumerate(zip(old.sources(c,former),src[:14])):
        if i!=12:assert sp.expand(before-after)==0
    q,Nsum,N=sp.symbols('q Nsum N')
    assert sp.expand((Nsum-N)+q*N-(Nsum+(q-1)*N))==0
    dag=schedule(tag.constants(2,(1,0,0)))
    assert old.counts(dag)==dict(operations=114,multiplications=55,additions=59)
    assert len(POSITIVE)==len(set(POSITIVE))==38 and len(src)==25
    old.kernel.verify_certificate()
    return dict(**old.counts(dag),positive_unknowns=38,equations=25,outer_equations=14,
                kernel_equations=11,fields=FIELDS,positive_coordinates=POSITIVE,
                parameters=PARAMETERS,dag=dag,sources=records,
                literal_nonpacking_source_maps=13,
                change='Delete one adapter and one content-sum addition; add the formal difference Nbar=Nsum-N. Reorder the content pair to the top and build fresh packed/Pell witnesses.')


def pair_regression():
    cases=negative=accepted=out_of_bound=0
    for q in (9,27,81,243,729):
        J=(q-1)//2
        for Nsum in range(1,(q-1)//4+1):
            for N in range(J+3):
                pair=Nsum+(q-1)*N
                # This upper bound follows after dropping the nonnegative
                # lower8 fields from P<=(q^10-1)/2.
                if 2*pair>=q*q:
                    out_of_bound+=1;continue
                assert N<=J
                Nb=Nsum-N
                lo,hi=pair%q,pair//q
                if Nb<0:
                    negative+=1
                    assert -q<Nb<0 and lo==q+Nb>J and hi==N-1
                    assert not tag.boolean(lo)
                if tag.boolean(pair):
                    accepted+=1
                    assert Nb>=0 and tag.boolean(N) and tag.boolean(Nb)
                cases+=1
    assert negative>0 and accepted>0
    return dict(top_pairs=cases,negative_complements_rejected=negative,
                Boolean_pairs_accepted=accepted,packing_upper_bound_rejections=out_of_bound,
                scope='Complete stated finite ranges for the top pair, including negative formal complements; no controller or history condition is substituted for the pair proof.')


def witness(beta,app,initial,words,ss,ds,final):
    c=tag.constants(beta,app)
    A=3**(1+max([len(initial)]+[len(w) for w in words]));R=c['C']*A
    t=len(words);q=R**t;H=(q-1)//(R-1)
    raw=dict.fromkeys(old.RAW,0)
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
    assert all(out[a]==out[b] for a,b in old.outer_comparisons())
    assert all(x>0 for key,x in env.items() if key not in PARAMETERS)
    assert all(0<=out[f]<q and tag.boolean(out[f]) for f in FIELDS)
    assert out['Nbar']==raw['Nbar'] and out['Nsum']>0
    assert out['Gstar']%3==1 and P<(D0-1)//2
    exponent=len(tag.trits(D0))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<D0 and D0<r*r
    # Restore the old positive source words and a new old-order pack/index.
    restored=dict(env,F_Nbar=out['Nbar']+1);del restored['Nsum']
    before0=old.run(old.prefix(c)[0][:-3],restored)
    Pold=before0[old.prefix(c)[1]];rold=Pold+(D0-1)//2
    restored.update(r=rold,betaP=D0-rold)
    before=old.run(old.prefix(c)[0],restored);before.update(K=c['K'],pell_tr1=2*rold+1)
    assert all(before[a]==before[b] for a,b in old.outer_comparisons())
    assert old.unit.valuation(rold)==exponent
    return dict(rows=t,parity=r%2,Nsum=env['Nsum'],Nbar_zero=out['Nbar']==0,
                repacked_index_changed=r!=rold)


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
                        cases+=1;rows+=z['rows'];zeros+=z['Nbar_zero']
                        changed+=z['repacked_index_changed'];parities[z['parity']]+=1
    post=witness(2,(1,0,0),(0,0),[(0,0),(0,),()],[0,0,1],[0,0,1],(0,))
    assert min(parities)>0 and zeros>0 and changed>0
    return dict(canonical_histories=cases,rows=rows,cutoff_unclassified=unresolved,
                kernel_index_parities=parities,zero_complement_histories=zeros,
                changed_packed_indices=changed,post_halt_example={k:v for k,v in post.items() if k!='Nsum'},
                new_outer_comparisons=14,restored_outer_comparisons=14,typed_fields=10,
                scope='Both packing orders and their exact native indices/valuations are freshly constructed. Huge positive Pell auxiliaries are proved by the kernel theorem, not materialized.')


def verify():
    return dict(status='PASS_POSITIVE_CONTENT_SUM_TAG',source=verify_source(),
                prepower=old.prepower(),top_pairs=pair_regression(),histories=histories(),
                review_status='Author plus independent root and binary complete proof/source reviews and fresh runs passed. Corrected weak packing-bound wording incorporated; no remaining findings. Mathematical construction and arithmetic frozen.',
                proof='../1980/EXPLORATION_POSITIVE_CONTENT_SUM_TAG.md',
                scope='Complete positive encoded-binary-word tag certificate, not a raw-input universal bound. New packing changes the Pell index; positive witnesses are rebuilt by the generic44 theorem.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:result['source'][k] for k in ['operations','multiplications','additions','positive_unknowns','equations']})
    print(result['top_pairs']);print(result['histories'])
