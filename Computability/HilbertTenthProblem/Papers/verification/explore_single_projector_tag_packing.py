"""Positive encoded-word tag certificate with explicit Gstar and packing costs."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_single_projector_tag_history as tag
import explore_tag_terminal_bound_recovery as reduced
import explore_parity_free_pell_kernel as kernel
import explore_unit_two_ternary_kernel as unit

RAW = 'Q S0 S1 M0 M1 N Nbar E Ebar'.split()
FIELDS = ['Gstar'] + RAW
POSITIVE = (['F_'+x for x in RAW] + ['F_Nfinal']
            + 'A H R L q Lfinal alphaI alphaH v r betaP'.split()
            + ['pell_'+x for x in kernel.AUXILIARIES])
PARAMETERS = ['Ninit', 'Linit']


def rename(x):
    if not isinstance(x,str): return x
    if x == 'D0': return 'scale'
    if x == 'r': return x
    return 'pell_'+x


def prefix(c):
    rows = [(x,'-','F_'+x,1) for x in RAW+['Nfinal']]
    rows += reduced.schedule(c)
    rows += [('Gstar','+','G','S0'), ('qm1','-','q',1),
             ('Rm1','-','R',1), ('head_product','*','H','Rm1'),
             ('radix_product','*','R','v'),
             ('q2','*','q','q'), ('q4','*','q2','q2'),
             ('q8','*','q4','q4'), ('scale','*','q8','q2')]
    last=FIELDS[-1]
    for i,f in enumerate(reversed(FIELDS[:-1])):
        rows += [(f'pack_mul{i}','*','q',last),
                 (f'pack_add{i}','+',f,f'pack_mul{i}')]
        last=f'pack_add{i}'
    rows += [('twiceP','+',last,last), ('index_rhs','+','scale','twiceP'),
             ('packed_bound','+','r','betaP')]
    return rows,last


def schedule(c):
    return prefix(c)[0] + [(rename(name),op,rename(a),rename(b))
                          for name,op,a,b in kernel.SCHEDULE]


def outer_comparisons():
    return reduced.comparisons()+[('head_product','qm1'),('radix_product','q'),
                                   ('pell_tr1','index_rhs'),('packed_bound','scale')]


def comparisons():
    return outer_comparisons()+[(rename(a),rename(b)) for a,b in kernel.EQUALITIES]


def run(rows,env):
    return tag.evaluate(rows,env)


def counts(rows):
    M=sum(op=='*' for _,op,_,_ in rows)
    return dict(operations=len(rows),multiplications=M,additions=len(rows)-M)


def sources(c,s):
    z=dict(s)
    for x in RAW+['Nfinal']: z[x]=s['F_'+x]-1
    A,H,Q,S0,S1,M0,M1,R,L,N,Nb,E,Eb,q,Ni,Li,Nt,Lt,ai,ah = [z[x] for x in
        'A H Q S0 S1 M0 M1 R L N Nbar E Ebar q Ninit Linit Nfinal Lfinal alphaI alphaH'.split()]
    P=sum((Q+A*H+S0 if f=='Gstar' else z[f])*q**i for i,f in enumerate(FIELDS))
    return [c['C']*A-R,S0+S1-H,2*Q+S1-M1,M0+M1-L,
            2*(N+Nb)+H-L,E+Eb-c['c']*H,
            R*(N-3*E-S1+c['U']*M1)-c['K']*(N-Ni+q*Nt),
            R*(M0+c['B']*M1)-c['Khalf']*(L-Li+q*Lt),
            Li+ai-A,Lt+ah-c['K'],H*(R-1)-q+1,R*z['v']-q,
            2*z['r']+1-q**10-2*P,z['r']+z['betaP']-q**10]


def verify_source():
    syms=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    c=dict(zip('C K Khalf B U c'.split(),sp.symbols('C K Khalf B U c')))
    env=run(schedule(c),syms);env['K']=c['K']
    src=sources(c,syms)
    sub={kernel.SYM[k]: (syms['q']**10 if k=='D0' else syms[rename(k)]) for k in kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in kernel.source_residuals()]
    src += core
    records=[]
    for i,((a,b),polynomial) in enumerate(zip(comparisons(),src)):
        actual=sp.expand(env[a]-env[b])
        correction=core[7]*(syms['pell_u']**2-syms['pell_y_aux']**2) if i==22 else 0
        assert sp.expand(actual-polynomial-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(polynomial),
                            correction=sp.sstr(correction)))
    dag=schedule(tag.constants(2,(1,0,0)))
    assert counts(dag)==dict(operations=115,multiplications=55,additions=60)
    assert len(POSITIVE)==len(set(POSITIVE))==38
    assert len(src)==len(comparisons())==25
    kernel.verify_certificate()
    return dict(**counts(dag),positive_unknowns=38,equations=25,outer_equations=14,
                kernel_equations=11,fields=FIELDS,parameters=PARAMETERS,
                positive_coordinates=POSITIVE,dag=dag,sources=records,
                groups=dict(tag=31,unit_guard=1,geometry=4,powers=4,packing=18,
                            index_and_bound=3,parity_free_kernel=44,positive_adapters=10),
                conditional_without_adapters=105,
                fixed_first_selector_without_adapters=104,
                fixed_native_prefix_without_adapters=106)


def prepower():
    cases=nonpower=0
    for beta in (1,2,3):
        c=tag.constants(beta,(1,0,0));K,C=c['K'],c['C']
        for A in range(K+1,K+8):
            R=C*A
            for j in range(3):
                H=1+j*R;q=R*(1+j*(R-1))
                assert H*(R-1)==q-1 and q%R==0 and R>K*K
                assert 2*K*K<3*R-K  # L < K^2*q/(3R-K) < q/2.
                assert 3*(A+1)<C*A-1
                assert c['c']<R-1
                scale=q**10;lo=(scale-1)//2
                assert scale>=81 and lo>=27 and scale<lo*lo
                n=q
                while n%3==0:n//=3
                nonpower+=n!=1;cases+=1
    return dict(rational_bound_cases=cases,nonpower_q_cases=nonpower,
                scope='Exact pre-power geometry and rational-bound inequalities, not claimed full source solutions.')


def compact_prefix_witness(beta,appendant,initial,words,selectors,prefixes,final):
    c=tag.constants(beta,appendant)
    A=3**(1+max([len(initial)]+[len(w) for w in words]))
    R=c['C']*A;t=len(words);q=R**t;H=(q-1)//(R-1)
    raw=dict.fromkeys(RAW,0)
    for i,(w,sel,d) in enumerate(zip(words,selectors,prefixes)):
        wt=R**i;mark=3**len(w);ns=(mark-1)//2;n=tag.value(w)
        raw['Q']+=sel*ns*wt;raw['S'+str(sel)]+=wt;raw['M'+str(sel)]+=mark*wt
        raw['N']+=n*wt;raw['Nbar']+=(ns-n)*wt
        e=(d-sel)//3;raw['E']+=e*wt;raw['Ebar']+=(c['c']-e)*wt
    env={'F_'+k:v+1 for k,v in raw.items()}
    env.update(F_Nfinal=tag.value(final)+1,A=A,H=H,R=R,L=raw['M0']+raw['M1'],q=q,
               Lfinal=3**len(final),Ninit=tag.value(initial),Linit=3**len(initial),
               alphaI=A-3**len(initial),alphaH=c['K']-3**len(final),v=q//R)
    env0=run(prefix(c)[0][:-3],env)
    P=env0[prefix(c)[1]];scale=q**10;r=P+(scale-1)//2
    env.update(r=r,betaP=scale-r)
    out=run(prefix(c)[0],env);out.update(K=c['K'],pell_tr1=2*r+1)
    assert all(out[a]==out[b] for a,b in outer_comparisons())
    assert all(value>0 for key,value in env.items() if key not in PARAMETERS)
    assert all(0<=out[f]<q and tag.boolean(out[f]) for f in FIELDS)
    assert out['Gstar']%3==1 and tag.boolean(out['G'])
    assert P==sum(out[f]*q**i for i,f in enumerate(FIELDS)) and P<(scale-1)//2
    exponent=len(tag.trits(scale))-1
    assert unit.mask_expected(r,exponent) and unit.valuation(r)==exponent
    assert 27<=r<scale and scale<r*r
    return dict(rows=t,parity=r%2,first_selector=selectors[0],
                zero_raw_fields=sum(out[x]==0 for x in RAW),zero_terminal=out['Nfinal']==0)


def histories():
    cases=rows=unresolved=zeros=zero_final=0;parities=[0,0];selectors=[0,0]
    for beta in (1,2,3):
        for a in (1,2,3):
            for app in product((0,1),repeat=a):
                for n in range(beta,beta+3):
                    for initial in product((0,1),repeat=n):
                        w=tuple(initial);words=[];ss=[];ds=[]
                        for _ in range(20):
                            if len(w)<beta:break
                            words.append(w);ss.append(w[0]);ds.append(tag.value(w[:beta]))
                            w=w[beta:]+(app if w[0] else (0,))
                        if len(w)>=beta:unresolved+=1;continue
                        z=compact_prefix_witness(beta,app,initial,words,ss,ds,w)
                        cases+=1;rows+=z['rows'];parities[z['parity']]+=1
                        selectors[z['first_selector']]+=1;zeros+=z['zero_raw_fields']
                        zero_final+=z['zero_terminal']
    post=compact_prefix_witness(2,(1,0,0),(0,0),[(0,0),(0,),()], [0,0,1],[0,0,1],(0,))
    assert min(parities)>0 and min(selectors)>0 and zero_final>0 and zeros>0
    return dict(canonical_histories=cases,rows=rows,cutoff_unclassified=unresolved,
                kernel_index_parities=parities,first_selectors=selectors,
                zero_word_coordinates=zeros,zero_terminal_histories=zero_final,
                post_halt_example=post,outer_comparisons_per_case=14,typed_fields_per_case=10,
                scope='All actual outer coordinates, native indices and valuations are constructed. The seventeen enormous positive Pell auxiliaries are supplied by the proved kernel converse, not materialized.')


def unit_and_carry_obstructions():
    # Four length-two inputs all halt after one step for beta=2, u=0.
    # Every original field has unit zero in at least one such source row.
    samples=[]
    for s,e in product((0,1),repeat=2):
        R,A,H,K=729,27,1,9;L=9;Q=4*s;N=s+3*e;Nb=4-N
        v=dict(Q=Q,S0=1-s,S1=s,M0=(1-s)*L,M1=s*L,G=Q+A,
               N=N,Nbar=Nb,E=e,Ebar=1-e)
        assert all(tag.boolean(x) for x in v.values())
        assert (v['G']+v['S0'])%3==1
        samples.append(v)
    assert all(any(v[f]%3==0 for v in samples) for f in tag.FIELDS)
    # Only a packing obstruction: this does not satisfy the tag sources.
    q=81;P=q+1;scale=q**10;r=P+(scale-1)//2
    assert tag.boolean(P) and P%3==1 and r<scale
    assert unit.valuation(r)==10*4 and P>=q
    return dict(no_uniform_unit_in_original_fields=True,local_rows=samples,
                unrestricted_first_field_carry=dict(q=q,first_field=P,other_fields=0,
                    valuation=40,scope='Packing and kernel-bound alias only; not a tag-source counterexample.'))


def verify():
    return dict(status='PASS_POSITIVE_ENCODED_WORD_TAG_PACKING',source=verify_source(),
                prepower=prepower(),histories=histories(),obstructions=unit_and_carry_obstructions(),
                review_status='Author verification plus root and binary independent complete proof/source reviews and fresh verification runs passed without findings. Mathematical construction and arithmetic frozen.',
                proof='../1980/EXPLORATION_SINGLE_PROJECTOR_TAG_PACKING.md',
                scope='Exact positive 115-operation certificate for the specified encoded binary word and fixed binary tag program. The pair (Ninit,Linit) must encode that word; ordinary numerical input conversion and a suitable universal startup are not provided. No new universal bound.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:result['source'][k] for k in ['operations','multiplications','additions','positive_unknowns','equations']})
    print(result['prepower']);print(result['histories'])
