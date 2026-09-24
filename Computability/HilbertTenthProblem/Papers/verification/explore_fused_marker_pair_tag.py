"""Fuse the implicit M0/M1 pair without changing the packed integer."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_implicit_unselected_marker_tag as previous

old=previous.old
tag=previous.tag
RAW=previous.RAW
FIELDS=previous.FIELDS
POSITIVE=previous.POSITIVE
PARAMETERS=previous.PARAMETERS


def prefix(c):
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name=='M0' or name in ('pack_mul3','pack_add3','pack_mul4'):continue
        if name=='l_append':
            rows.append((name,'*',c['B']-1,'M1'))
        elif name=='l_output':
            rows.append((name,'+','L','l_append'))
        elif name=='pack_add4':
            rows += [('marker_scaled','*','qm1','M1'),
                     ('marker_pair','+','L','marker_scaled'),
                     ('higher_scaled','*','q2','pack_add2'),
                     ('pack_add4','+','marker_pair','higher_scaled')]
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
    for name in ('l_output','l_left','pack_add4',prefix(c)[1],'index_rhs','packed_bound'):
        assert sp.expand(env[name]-before[name])==0,name
    assert all('M0' not in (n,a,b) for n,_,a,b in prefix(c)[0])
    q,L,M1,B,rest=sp.symbols('q L M1 B rest')
    assert sp.expand((L-M1)+B*M1-(L+(B-1)*M1))==0
    assert sp.expand((L-M1)+q*(M1+q*rest)-(L+(q-1)*M1+q*q*rest))==0
    dag=schedule(tag.constants(2,(1,0)))
    assert old.counts(dag)==dict(operations=109,multiplications=55,additions=54)
    assert len(POSITIVE)==len(set(POSITIVE))==34
    return dict(**old.counts(dag),positive_unknowns=34,equations=21,outer_equations=10,
                kernel_equations=11,positive_coordinates=POSITIVE,fields=FIELDS,
                parameters=PARAMETERS,dag=dag,sources=records,
                identical_sources=True,identical_packed_integer=True,
                M0='Proof abbreviation L-M1; no runtime register or instruction',
                contract='Appendants have length at least two, inherited exactly from110.')


def finite_identities():
    cases=negative=0
    for q in (3,5,9,27):
        for L in range(1,8):
            for M1 in range(8):
                for rest in (-2,0,3):
                    for B in (3,9):
                        M0=L-M1
                        assert M0+B*M1==L+(B-1)*M1
                        assert M0+q*(M1+q*rest)==L+(q-1)*M1+q*q*rest
                        cases+=1;negative+=M0<0
    return dict(identity_cases=cases,negative_M0_cases=negative,
                scope='Unrestricted algebraic regrouping, including negative M0, a nonpower q and signed higher blocks. Not full source tuples.')


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
    assert 'M0' not in out
    assert all(out[a]==out[b] for a,b in outer_comparisons())
    assert all(x>0 for key,x in env.items() if key not in PARAMETERS)
    conceptual=dict(out,M0=out['L']-out['M1'])
    assert conceptual['M0']==raw['M0'] and out['Ebar']==raw['Ebar'] and out['Nbar']==raw['Nbar']
    assert all(0<=conceptual[f]<q and tag.boolean(conceptual[f]) for f in FIELDS)
    assert P==sum(conceptual[f]*q**i for i,f in enumerate(FIELDS))
    exponent=len(tag.trits(scale))-1
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<scale and scale<r*r
    before=old.run(previous.prefix(c)[0],env);before.update(K=c['K'],pell_tr1=2*r+1)
    assert all(before[a]==before[b] for a,b in previous.outer_comparisons())
    for name in ('l_output','l_left','pack_add4',prefix(c)[1],'index_rhs','packed_bound'):
        assert before[name]==out[name]
    return dict(rows=t,parity=r%2,M0_zero=conceptual['M0']==0,index_preserved=True)


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
                predecessor_outer_comparisons=10,conceptual_typed_fields=10,
                scope='Fresh actual109 and110 prefix evaluation on identical supplied coordinates. All packed values, indices and kernel coordinates are preserved; M0 is only reconstructed for verification.')


def verify():
    return dict(status='PASS_FUSED_MARKER_PAIR_TAG',source=verify_source(),
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; construction and arithmetic frozen.',
                identities=finite_identities(),histories=histories(),
                proof='../1980/EXPLORATION_FUSED_MARKER_PAIR_TAG.md',
                scope='Exact109 arithmetic successor to110 with identical positive source solutions. The appendant-length restriction a>=2 and encoded-input boundary are unchanged.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:result['source'][k] for k in ['operations','multiplications','additions','positive_unknowns','equations']})
    print(result['identities']);print(result['histories'])
