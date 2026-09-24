"""Reuse the already computed 2Q in the four low conceptual mask fields."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_fused_complement_pairs_tag as previous

old=previous.old
tag=previous.tag
RAW=previous.RAW
FIELDS=previous.FIELDS
POSITIVE=previous.POSITIVE
PARAMETERS=previous.PARAMETERS
REMOVED=('padding','G','S0','Gstar','M0','Ebar','Nbar')


def prefix(c):
    rows=[]
    skipped={f'pack_{kind}{i}' for i in range(5,9) for kind in ('mul','add')}
    for name,op,a,b in previous.prefix(c)[0]:
        if name=='pack_add8':
            rows += [('head_coefficient0','+','A','q2'),
                     ('head_coefficient','+','head_coefficient0',1),
                     ('head_term','*','H','head_coefficient'),
                     ('selector_scaled','*','q2','S1'),
                     ('selector_inner','+','Q','selector_scaled'),
                     ('selector_term','*','qm1','selector_inner'),
                     ('selector_residual','-','twice_Q','S1'),
                     ('upper_shifted','*','q4','pack_add4'),
                     ('low_join0','+','head_term','selector_term'),
                     ('low_join1','+','low_join0','selector_residual'),
                     ('pack_add8','+','low_join1','upper_shifted')]
        elif name in REMOVED or name in skipped:continue
        else:rows.append((name,op,a,b))
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in old.kernel.SCHEDULE]


outer_comparisons=previous.outer_comparisons
comparisons=previous.comparisons
sources=previous.sources


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
    before=old.run(previous.prefix(c)[0],s)
    for name in ('l_left','pack_add4',prefix(c)[1],'index_rhs','packed_bound','twice_Q'):
        assert sp.expand(env[name]-before[name])==0,name
    for removed in REMOVED:
        assert all(removed not in (n,a,b) for n,_,a,b in prefix(c)[0])
    assert sum(n=='twice_Q' for n,_,_,_ in prefix(c)[0])==1
    q,A,H,Q,S1,rest=sp.symbols('q A H Q S1 rest')
    S0=H-S1;Gstar=Q+A*H+S0
    lhs=Gstar+q*Q+q*q*S0+q**3*S1+q**4*rest
    rhs=H*(A+q*q+1)+(q-1)*(Q+q*q*S1)+(2*Q-S1)+q**4*rest
    assert sp.expand(lhs-rhs)==0
    dag=schedule(tag.constants(2,(1,0)))
    assert old.counts(dag)==dict(operations=106,multiplications=54,additions=52)
    assert len(POSITIVE)==len(set(POSITIVE))==34
    low=prefix(c)[0][-14:-3]
    assert old.counts(low)==dict(operations=11,multiplications=4,additions=7)
    return dict(**old.counts(dag),positive_unknowns=34,equations=21,outer_equations=10,
                kernel_equations=11,positive_coordinates=POSITIVE,fields=FIELDS,
                parameters=PARAMETERS,dag=dag,sources=records,
                identical_sources=True,identical_packed_integer=True,
                new_low_group=old.counts(low),old_low_group=dict(operations=12,multiplications=5,additions=7),
                reused_register='twice_Q=2Q, already required to compute M1',
                conceptual_registers={'S0':'H-S1','Gstar':'Q+A*H+H-S1','M0':'L-M1','Ebar':'cH-E','Nbar':'Nsum-N'},
                contract='Appendants have length at least two and the original encoded-input contract; all source solutions are exactly those of107.')


def finite_identities():
    cases=negative_s0=negative_guard=negative_residual=0
    for q in (3,5,9,27):
        for A in (1,2,4):
            for H in (1,2):
                for Q in range(5):
                    for S1 in range(7):
                        for rest in (-3,0,4):
                            S0=H-S1;guard=Q+A*H+S0
                            lhs=guard+q*Q+q*q*S0+q**3*S1+q**4*rest
                            rhs=H*(A+q*q+1)+(q-1)*(Q+q*q*S1)+(2*Q-S1)+q**4*rest
                            assert lhs==rhs
                            cases+=1;negative_s0+=S0<0;negative_guard+=guard<0;negative_residual+=2*Q<S1
    return dict(identity_cases=cases,negative_S0_cases=negative_s0,
                negative_Gstar_cases=negative_guard,negative_residual_cases=negative_residual,
                scope='Unrestricted exact identity with signed conceptual fields, signed higher blocks and nonpower q; not full source tuples.')


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
    assert all(x not in out for x in REMOVED)
    assert all(out[a]==out[b] for a,b in outer_comparisons())
    assert all(x>0 for key,x in env.items() if key not in PARAMETERS)
    conceptual=dict(out,S0=H-out['S1'],Gstar=out['Q']+A*H+H-out['S1'],
                    M0=out['L']-out['M1'],Ebar=c['c']*H-out['E'],Nbar=out['Nsum']-out['N'])
    assert all(conceptual[f]==raw[f] for f in ('S0','M0','Ebar','Nbar'))
    assert all(0<=conceptual[f]<q and tag.boolean(conceptual[f]) for f in FIELDS)
    assert P==sum(conceptual[f]*q**i for i,f in enumerate(FIELDS))
    exponent=len(tag.trits(scale))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<scale and scale<r*r
    before=old.run(previous.prefix(c)[0],env);before.update(K=c['K'],pell_tr1=2*r+1)
    assert all(before[a]==before[b] for a,b in previous.outer_comparisons())
    for name in ('l_left','pack_add4',prefix(c)[1],'index_rhs','packed_bound','twice_Q'):
        assert before[name]==out[name]
    return dict(rows=t,parity=r%2,zero_conceptual=[conceptual[f]==0 for f in ('S0','M0','Ebar','Nbar')],
                residual_negative=out['selector_residual']<0,index_preserved=True)


def histories():
    cases=rows=unresolved=negative=0;zeros=[0,0,0,0];parities=[0,0]
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
                        cases+=1;rows+=z['rows'];parities[z['parity']]+=1;negative+=z['residual_negative']
                        zeros=[x+int(y) for x,y in zip(zeros,z['zero_conceptual'])]
    post=witness(2,(1,0,0),(0,0),[(0,0),(0,),()],[0,0,1],[0,0,1],(0,))
    assert min(zeros)>0 and min(parities)>0
    return dict(canonical_histories=cases,rows=rows,cutoff_unclassified=unresolved,
                kernel_index_parities=parities,zero_conceptual_counts=dict(zip(('S0','M0','Ebar','Nbar'),zeros)),
                negative_canonical_residuals=negative,preserved_indices=cases,post_halt_example=post,
                new_outer_comparisons=10,predecessor_outer_comparisons=10,conceptual_typed_fields=10,
                scope='Fresh actual106 and107 prefixes on identical supplied coordinates. All packed values, indices and kernel coordinates are preserved. Removed conceptual fields are reconstructed only for verification.')


def verify():
    return dict(status='PASS_SHARED_MARKER_LOW_PACKING',source=verify_source(),
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; construction and arithmetic frozen.',
                identities=finite_identities(),histories=histories(),
                proof='../1980/EXPLORATION_SHARED_MARKER_LOW_PACKING.md',
                scope='Exact106 arithmetic successor to107 with identical positive source solutions and ten conceptual masks. The a>=2 appendant restriction and encoded-input boundary are unchanged.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:result['source'][k] for k in ['operations','multiplications','additions','positive_unknowns','equations']})
    print(result['identities']);print(result['histories'])
