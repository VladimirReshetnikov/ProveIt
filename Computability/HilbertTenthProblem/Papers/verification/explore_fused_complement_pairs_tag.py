"""Fold Ebar and Nbar into their only uses in the unchanged ten-field packing."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_fused_marker_pair_tag as previous

old=previous.old
tag=previous.tag
RAW=previous.RAW
FIELDS=previous.FIELDS
POSITIVE=previous.POSITIVE
PARAMETERS=previous.PARAMETERS


def prefix(c):
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name in ('Ebar','Nbar','pack_mul1','pack_add1','pack_mul2'):continue
        if name=='pack_mul0':
            rows.append((name,'*','qm1','N'))
        elif name=='pack_add0':
            rows.append((name,'+','Nsum','pack_mul0'))
        elif name=='pack_add2':
            rows += [('prefix_scaled','*','qm1','E'),
                     ('prefix_pair','+','prefix_scale','prefix_scaled'),
                     ('content_shifted','*','q2','pack_add0'),
                     ('pack_add2','+','prefix_pair','content_shifted')]
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
    for name in ('l_left','pack_add0','pack_add2','pack_add4',prefix(c)[1],'index_rhs','packed_bound'):
        assert sp.expand(env[name]-before[name])==0,name
    for removed in ('M0','Ebar','Nbar'):
        assert all(removed not in (n,a,b) for n,_,a,b in prefix(c)[0])
    q,Nsum,N,cH,E,rest=sp.symbols('q Nsum N cH E rest')
    assert sp.expand((Nsum-N)+q*N-(Nsum+(q-1)*N))==0
    assert sp.expand((cH-E)+q*(E+q*rest)-(cH+(q-1)*E+q*q*rest))==0
    dag=schedule(tag.constants(2,(1,0)))
    assert old.counts(dag)==dict(operations=107,multiplications=55,additions=52)
    assert len(POSITIVE)==len(set(POSITIVE))==34
    return dict(**old.counts(dag),positive_unknowns=34,equations=21,outer_equations=10,
                kernel_equations=11,positive_coordinates=POSITIVE,fields=FIELDS,
                parameters=PARAMETERS,dag=dag,sources=records,
                identical_sources=True,identical_packed_integer=True,
                conceptual_registers={'M0':'L-M1','Ebar':'cH-E','Nbar':'Nsum-N'},
                contract='Appendants have length at least two, inherited exactly from109/110.')


def finite_identities():
    cases=negative_content=negative_prefix=0
    for q in (3,5,9,27):
        for Nsum in range(1,8):
            for N in range(8):
                assert Nsum-N+q*N==Nsum+(q-1)*N
                negative_content+=Nsum<N
                for base in range(5):
                    for E in range(8):
                        for rest in (-2,0,3):
                            assert base-E+q*(E+q*rest)==base+(q-1)*E+q*q*rest
                            cases+=1;negative_prefix+=base<E
    return dict(joint_identity_cases=cases,negative_content_pair_cases=negative_content,
                negative_prefix_cases=negative_prefix,
                scope='Exact regroupings before any mask, with negative formal complements, nonpower q and signed higher blocks. Not full source tuples.')


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
    assert all(x not in out for x in ('M0','Ebar','Nbar'))
    assert all(out[a]==out[b] for a,b in outer_comparisons())
    assert all(x>0 for key,x in env.items() if key not in PARAMETERS)
    conceptual=dict(out,M0=out['L']-out['M1'],Ebar=c['c']*H-out['E'],Nbar=out['Nsum']-out['N'])
    assert all(conceptual[f]==raw[f] for f in ('M0','Ebar','Nbar'))
    assert all(0<=conceptual[f]<q and tag.boolean(conceptual[f]) for f in FIELDS)
    assert P==sum(conceptual[f]*q**i for i,f in enumerate(FIELDS))
    exponent=len(tag.trits(scale))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<scale and scale<r*r
    before=old.run(previous.prefix(c)[0],env);before.update(K=c['K'],pell_tr1=2*r+1)
    assert all(before[a]==before[b] for a,b in previous.outer_comparisons())
    for name in ('l_left','pack_add0','pack_add2','pack_add4',prefix(c)[1],'index_rhs','packed_bound'):
        assert before[name]==out[name]
    return dict(rows=t,parity=r%2,zero_conceptual=[conceptual[f]==0 for f in ('M0','Ebar','Nbar')],
                index_preserved=True)


def histories():
    cases=rows=unresolved=0;zeros=[0,0,0];parities=[0,0]
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
                        cases+=1;rows+=z['rows'];parities[z['parity']]+=1
                        zeros=[x+int(y) for x,y in zip(zeros,z['zero_conceptual'])]
    post=witness(2,(1,0,0),(0,0),[(0,0),(0,),()],[0,0,1],[0,0,1],(0,))
    assert min(zeros)>0 and min(parities)>0
    return dict(canonical_histories=cases,rows=rows,cutoff_unclassified=unresolved,
                kernel_index_parities=parities,zero_conceptual_counts=dict(zip(('M0','Ebar','Nbar'),zeros)),
                preserved_indices=cases,post_halt_example=post,new_outer_comparisons=10,
                predecessor_outer_comparisons=10,conceptual_typed_fields=10,
                scope='Fresh actual107 and109 prefix evaluation on identical supplied coordinates. All packed values, indices and kernel coordinates are preserved; the three removed registers are only proof abbreviations.')


def verify():
    return dict(status='PASS_FUSED_COMPLEMENT_PAIRS_TAG',source=verify_source(),
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; construction and arithmetic frozen.',
                identities=finite_identities(),histories=histories(),
                proof='../1980/EXPLORATION_FUSED_COMPLEMENT_PAIRS_TAG.md',
                scope='Exact107 arithmetic successor to109 with identical positive source solutions and ten conceptual masks. The appendant-length restriction a>=2 and encoded-input boundary are unchanged.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:result['source'][k] for k in ['operations','multiplications','additions','positive_unknowns','equations']})
    print(result['identities']);print(result['histories'])
