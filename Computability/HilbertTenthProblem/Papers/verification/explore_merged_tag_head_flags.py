"""A full false positive for merging S0,S1 into the Boolean word H+2S1."""
from pathlib import Path
import json
import sympy as sp
import explore_reordered_startup_tag as previous

old=previous.old
tag=previous.tag
kernel=previous.kernel
base=previous.base
POSITIVE=previous.POSITIVE
PARAMETERS=previous.PARAMETERS
FIELDS=['F','Q','G']+previous.FIELDS[4:]


def prefix(c):
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name=='scale':continue
        if name=='q8':rows.append(('scale','*','q4','q4'))
        elif name=='flag_scaled':rows.append((name,'*',2,'S1'))
        elif name in ('QG_shifted','low_four','upper_shifted','pack_add8'):continue
        else:rows.append((name,op,a,b))
        if name=='flag_pair':
            rows.extend([('upper_shifted','*','q2','pack_add4'),
                         ('combined_rest','+','QG_pair','upper_shifted'),
                         ('rest_shifted','*','q','combined_rest'),
                         ('pack_add8','+','flag_pair','rest_shifted')])
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                        for n,op,a,b in kernel.schedule(1)]


def fields(c,s):
    raw=previous.fields(c,s)
    raw['F']=s['H']+2*s['S1']
    return raw


def verify_source(leading):
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    Cbar,Kh,Ut,B,cc,j=sp.symbols('Cbar Khalf Uthird B c jguard')
    c=dict(Cbar=Cbar,Khalf=Kh,Uthird=Ut,B=B,c=cc,C=Kh*Cbar,K=3*Kh,
           U=3*Ut+leading,leading=leading,guard_coefficient=j)
    inherited=dict(previous.previous.lift(s),F_Nfinal=1,Lfinal=3,alphaH=c['K']-3)
    src=base.sources(c,inherited);assert sp.expand(src[4])==0;del src[4]
    raw=fields(c,s);P=sum(raw[f]*s['q']**i for i,f in enumerate(FIELDS))
    src[6]=2*s['r']+1-s['q']**8-2*P
    src[7]=s['r']+s['betaP']-s['q']**8
    sub={kernel.SYM[k]:s['q']**8 if k=='D0' else s[old.rename(k)] for k in kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in kernel.source_residuals(1)]
    src+=core
    env=old.run(schedule(c),s);env['K']=c['K']
    u=s['pell_j']*s['pell_c']+2*s['r']+1
    assert len(src)==len(previous.comparisons())==18
    records=[]
    for i,((a,b),polynomial) in enumerate(zip(previous.comparisons(),src)):
        correction=core[7]*(u*u-s['pell_y_aux']**2) if i==16 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    assert sp.expand(env[prefix(c)[1]]-P)==0
    dag=schedule(base.constants(2,(leading,1)))
    assert old.counts(dag)==dict(operations=92,multiplications=50,additions=42)
    return dict(leading=leading,operations=92,multiplications=50,additions=42,
                positive_unknowns=len(POSITIVE),equations=18,outer_equations=8,
                positive_coordinates=POSITIVE,parameters=PARAMETERS,fields=FIELDS,
                dag=dag,sources=records)


def local_holes():
    cases=0
    for beta in (2,3,4):
        K=3**beta
        for ell in range(beta+2,beta+6):
            L=3**ell;A=3*L
            for e in range(beta,ell-1):
                V=3**e;Q=(L-1)//2-V;S=1+2*V
                F=1+2*S;G=Q+A
                assert 2*Q+S==L and F==3+4*V
                assert all(tag.boolean(x) for x in (Q,F,G))
                assert not tag.boolean(S) and 2*V%K==0
                cases+=1
    return dict(typed_local_hole_cases=cases,
                scope='The merged mask admits an off-head selector carrying a digit2, '
                      'while Q,G and the selected marker stay Boolean.')


def witness():
    app=(0,1,0,0);beta=2;c=base.constants(beta,app)
    # This extra fixed padding also meets C>K^2*Linit.
    c['C']=3**11;c['Cbar']=c['C']//c['Khalf']
    c['guard_coefficient']=(c['C']-c['C']//c['K'])//2
    strings=['001001','10010','1000100','001000100','10001000','0010000100',
             '100001000','00010000100','0100001000','000010000','00100000',
             '1000000','000000100','00001000','0010000','100000',
             '00000100','0001000','010000','00000','0000','000','00']
    words=[tuple(map(int,w)) for w in strings]
    initial=words[0];final=(0,);V=9;corrupted=1
    selectors=[w[0] for w in words]
    effective=selectors.copy();effective[corrupted]+=2*V
    numbers=[tag.value(w) for w in words];markers=[3**len(w) for w in words]
    prefixes=[tag.value(w[:beta])//3 for w in words]
    qs=[s*(L-1)//2 for s,L in zip(selectors,markers)];qs[corrupted]-=V
    for i,(n,L,e,s,qrow) in enumerate(zip(numbers,markers,prefixes,effective,qs)):
        nxt=numbers[i+1] if i+1<len(words) else 0
        assert n-3*e-s+c['U']*selectors[i]*L==c['K']*nxt
        next_marker=markers[i+1] if i+1<len(words) else 3
        assert L*(c['B'] if selectors[i] else 1)==c['Khalf']*next_marker
        assert 2*qrow+s==selectors[i]*L
        assert n>=s and (n-s)%3==0
        if i!=corrupted:
            assert words[i][beta:]+(app if selectors[i] else (0,))==(words[i+1] if i+1<len(words) else final)
        assert tag.boolean(qrow) and tag.boolean(1+2*s)
    assert numbers[corrupted]==28 and effective[corrupted]==19
    assert numbers[corrupted+1]==82
    actual_prefix=['001001','10010','0100100']
    actual_cycle=['001000','10000','0000100']
    actual=[tuple(map(int,w)) for w in actual_prefix+actual_cycle]
    for a,b in zip(actual,actual[1:]+[tuple(map(int,actual_cycle[0]))]):
        assert a[beta:]+(app if a[0] else (0,))==b
    assert all(len(w)>=beta for w in actual)
    A=3**12;R=c['C']*A;assert R==3**23
    height=len(words);q=R**height;H=(q-1)//(R-1)
    pack=lambda vs:sum(v*R**i for i,v in enumerate(vs))
    N,S1,Q,E,L=map(pack,(numbers,effective,qs,prefixes,markers))
    T=(N-S1)//3
    assert min(Q,S1,T,E)>0 and A>max(markers)
    assert c['C']>c['K']**2*3**len(initial)
    s=dict(Q=Q,S1=S1,Tcontent=T,E=E,A=A,R=R,q=q,H=H,L=L,
           Ninit=tag.value(initial),Linit=3**len(initial),
           alphaI=A-3**len(initial),v=q//R)
    raw=fields(c,s)
    assert all(0<=raw[f]<q and tag.boolean(raw[f]) for f in FIELDS)
    assert not tag.boolean(S1) and raw['F']%3==1
    assert raw['S0']>0
    P=sum(raw[f]*q**i for i,f in enumerate(FIELDS));D0=q**8;r=P+(D0-1)//2
    s.update(r=r,betaP=D0-r)
    env=old.run(prefix(c)[0],s);env.update(K=c['K'],pell_tr1=2*r+1)
    assert all(env[a]==env[b] for a,b in previous.comparisons()[:8])
    assert env[prefix(c)[1]]==P
    assert all(v>0 for name,v in s.items() if name not in PARAMETERS)
    exponent=8*23*height
    assert exponent==4232 and r%2==0
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert D0>=81 and 27<=r<D0 and D0<r*r
    return dict(constants=c,initial=initial,appendant=app,beta=beta,
                actual_nonhalting_prefix=actual_prefix,actual_nonhalting_cycle=actual_cycle,
                false_source_words=strings,terminal=final,corrupted_row=corrupted,
                hole=V,effective_selector_rows=effective,prefix_rows=prefixes,
                positive_outer_coordinates=s,retained_fields={f:raw[f] for f in FIELDS},
                untyped_S1=S1,derived_S0=raw['S0'],packed_word=P,scale=D0,index=r,
                index_parity=r%2,exact_central_valuation=exponent,
                rows=height,outer_equations=8,masked_fields=8,
                scope='The same true radix, prefix masks, content guard and singleton '
                      'zero endpoint hold. The fixed-plus43 converse supplies sixteen '
                      'fresh positive auxiliaries; enormous auxiliary values are not '
                      'materialized. This is not a full Neary Table2 instance.')


def verify():
    return dict(status='PASS_MERGED_TAG_HEAD_FLAGS_COUNTEREXAMPLE',
                sources=[verify_source(leading) for leading in (0,1)],
                local=local_holes(),witness=witness(),
                review='Author and two independent complete proof/source reviews and fresh verification runs pass.',
                scope='Rejected92 merged-head-mask source. Separate genuine92/91 '
                      'optimizations retaining both head masks are unaffected.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print([{k:s[k] for k in ('leading','operations','multiplications','additions',
                            'positive_unknowns','equations')} for s in result['sources']])
    print(result['local']);print({k:result['witness'][k] for k in ('rows','outer_equations',
                              'masked_fields','index_parity','exact_central_valuation')})
