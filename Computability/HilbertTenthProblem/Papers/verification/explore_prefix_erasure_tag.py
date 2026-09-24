"""Deleting Ebar permits whole-content erasure, including normalized inputs."""
from pathlib import Path
import json
import sympy as sp
import explore_product_coordinate_tag as previous

old=previous.old
tag=previous.tag
kernel=previous.kernel
POSITIVE=previous.POSITIVE
PARAMETERS=previous.PARAMETERS
FIELDS=[f for f in previous.FIELDS if f!='Ebar']
comparisons=previous.comparisons


def prefix(c):
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name in ('prefix_scale','prefix_scaled','prefix_pair','scale'):continue
        if name=='q8':rows.append(('scale','*','q4','q4'))
        elif name=='content_shifted':rows.append((name,'*','q','pack_add0'))
        elif name=='pack_add2':rows.append((name,'+','E','content_shifted'))
        else:rows.append((name,op,a,b))
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in kernel.schedule(1)]


def verify_source(leading):
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    C,Kh,Ut,B,cc,j=sp.symbols('C Khalf Uthird B c jguard')
    c=dict(C=C,Cbar=C/Kh,Khalf=Kh,Uthird=Ut,B=B,c=cc,K=3*Kh,
           U=3*Ut+leading,leading=leading,guard_coefficient=j)
    D,Z,Q,S,T,E,R,H,L,q,r=[s[n] for n in
                         ('transport_scale','AH','Q','S1','Tcontent','E','R','H','L','q','r')]
    N=3*T+S if leading==0 else 3*T-2*Q;M1=2*Q+S
    raw=previous.fields(c,s);P=sum(raw[f]*q**i for i,f in enumerate(FIELDS))
    src=[Kh*D-R,D*(T-E+Ut*M1)-N+s['Ninit'],
         D*(L+(B-1)*M1)-L+s['Linit']-3*q,
         R*H-H-q+1,R*H-C*Z,R*s['v']-q,
         2*r+1-q**8-2*P,r+s['betaP']-q**8]
    sub={kernel.SYM[n]:q**8 if n=='D0' else s[old.rename(n)] for n in kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in kernel.source_residuals(1)]
    src+=core;env=old.run(schedule(c),s);u=s['pell_j']*s['pell_c']+2*r+1
    records=[]
    assert len(src)==len(comparisons())==18
    for i,((a,b),p) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(u*u-s['pell_y_aux']**2) if i==16 else 0
        assert sp.expand(env[a]-env[b]-p-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(correction)))
    assert sp.expand(env[prefix(c)[1]]-P)==0
    dag=schedule(previous.constants(4,(leading,1,0,0)))
    assert old.counts(dag)==dict(operations=87,multiplications=47,additions=40)
    return dict(leading=leading,operations=87,multiplications=47,additions=40,
                positive_unknowns=len(POSITIVE),equations=18,outer_equations=8,
                positive_coordinates=POSITIVE,parameters=PARAMETERS,fields=FIELDS,
                dag=dag,sources=records)


def erased_trace(beta,app,initial):
    assert beta%2==0 and beta>=2 and len(app)>=2
    assert (len(app)-1)%(beta-1)==(len(initial)-1)%(beta-1)==0
    assert initial[0]==0 and tag.value(initial)//3>0
    w=initial;words=[];saw_one=False
    for _ in range(50):
        assert len(w)>=beta
        words.append(w)
        if saw_one and w[0]==0:break
        saw_one|=w[0]==1
        w=w[beta:]+(app if w[0] else (0,))
    else:raise AssertionError('No later zero in this bounded example')
    erased=len(words)-1
    w=(0,)*(len(w)-beta+1)
    while len(w)>=beta:
        words.append(w);w=w[beta:]+(0,)
    assert w==(0,)
    nums=[tag.value(w) for w in words];ss=[w[0] for w in words]
    es=[tag.value(w[:beta])//3 for w in words]
    es[erased]=nums[erased]//3
    K=3**beta;U=tag.value(app)
    for i,(word,n,si,e) in enumerate(zip(words,nums,ss,es)):
        next_n=nums[i+1] if i+1<len(words) else 0
        assert n-3*e-si+U*si*3**len(word)==K*next_n
        next_len=len(words[i+1]) if i+1<len(words) else 1
        assert next_len==len(word)-beta+(len(app) if si else 1)
        assert tag.boolean(e)
    return words,ss,es,erased


def witness(beta,app,initial):
    words,ss,es,erased=erased_trace(beta,app,initial)
    c=previous.constants(beta,app);Li=3**len(initial);C=c['C']
    while C<=c['K']**2*Li:C*=3
    c.update(C=C,Cbar=C//c['Khalf'],guard_coefficient=(C-C//c['K'])//2)
    ce=len(tag.trits(C))-1;h=beta-1
    m=max(ce+1+max(map(len,words)),2*h+3)
    if m%2==0:m+=1
    R=3**m;A=R//C;t=len(words);q0=R**t
    pack=lambda vs:sum(v*R**i for i,v in enumerate(vs))
    S=pack(ss);Q=pack([si*(3**len(w)-1)//2 for si,w in zip(ss,words)])
    E=pack(es);N=pack([tag.value(w) for w in words]);L0=pack([3**len(w) for w in words])
    T=(N-S)//3 if c['leading']==0 else (N+2*Q)//3
    assert min(Q,S,E,T)>0 and A>Li
    pair=[]
    for padded in (False,True):
        height=t+(m-h if padded else 0);q=R**height;H=(q-1)//(R-1)
        delta=q0*3*sum((R//c['Khalf'])**i for i in range(m)) if padded else 0
        s=dict(Q=Q,S1=S,E=E,Tcontent=T,transport_scale=R//c['Khalf'],AH=A*H,
               R=R,q=q,H=H,L=L0+delta,Ninit=tag.value(initial),Linit=Li,v=q//R)
        raw=previous.fields(c,s)
        assert all(0<=raw[f]<q and tag.boolean(raw[f]) for f in FIELDS)
        assert raw['S0']%3==1
        P=sum(raw[f]*q**i for i,f in enumerate(FIELDS));D0=q**8;r=P+(D0-1)//2
        s.update(r=r,betaP=D0-r)
        env=old.run(prefix(c)[0],s);env['pell_tr1']=2*r+1
        assert all(env[a]==env[b] for a,b in comparisons()[:8])
        assert env[prefix(c)[1]]==P
        assert all(v>0 for n,v in s.items() if n not in PARAMETERS)
        assert r%2==(N+E+L0+delta)%2
        assert old.unit.mask_expected(r,8*m*height) and old.unit.valuation(r)==8*m*height
        assert 27<=r<D0 and D0<r*r
        pair.append(dict(parity=r%2,height=height,valuation=8*m*height,
                         omitted_Ebar_Boolean=raw['Ebar']>=0 and tag.boolean(raw['Ebar'])))
    assert pair[0]['parity']!=pair[1]['parity']
    return dict(beta=beta,appendant=app,initial=initial,erased_row=erased,
                source_words=[''.join(map(str,w)) for w in words],rows=t,
                erased_prefix_quotient=es[erased],ordinary_prefix_bound=c['c'],
                false_erasure=es[erased]>c['c'],outer=pair,
                scope='All8 remaining masks and outer comparisons hold on both parity witnesses. '
                      'The even member has a fresh positive plus43 extension.')


def startup_arithmetic():
    cases=0
    for p in (1,2,3):
      beta=10*p
      for n in (0,1,4):
       for lam in (2,4,8):
        minimum=11*(p+n+beta-2)
        s=lam*(beta-1)+1
        while s<minimum:s+=beta-1
        a=beta*s;ell=a-beta+1
        assert ell%(beta-1)==a%(beta-1)==1
        # The final garbage code is b^4 c b^6. Its c and the following b
        # are original input-track reads s-7 and s-6, respectively.
        for i in (s-7,s-6,s-1):
            assert 0<=i<s and ell-i*(beta-1)>=s>=beta
        cases+=1
    return dict(normalized_startup_size_cases=cases,
                scope='Arithmetic checks of the primary-source track suffix and traversal bound; '
                      'not materialized Neary machines or derivation of those source facts.')


def verify():
    examples=[]
    for app in ((0,1,0,0),(1,0,0,0),(0,1),(1,0)):
        examples.append(witness(2,app,tuple(map(int,'001001'))))
    for beta in (4,10):
        a=2*beta-1;app=[0]*a;app[1]=app[beta+1]=1
        initial=[0]*a;initial[2]=initial[beta]=1
        examples.append(witness(beta,tuple(app),tuple(initial)))
    actual=[tuple(map(int,w)) for w in ('001001','10010','0100100','001000','10000','0000100')]
    for a,b in zip(actual,actual[1:]+[actual[3]]):
        assert a[2:]+((0,1,0,0) if a[0] else (0,))==b
        assert len(a)>=2
    assert examples[0]['false_erasure']
    return dict(status='PASS_PREFIX_ERASURE_TAG_COUNTEREXAMPLE',
                sources=[verify_source(e) for e in (0,1)],examples=examples,
                full_outer_tuples=2*len(examples),startup=startup_arithmetic(),
                certified_nonhalting_example=0,
                review='Author and two independent complete proof/source/dependency reviews and fresh verification PASS, including the primary-source Neary startup facts.',
                scope='Rejected87 Ebar-deletion source. Whole-content erasure gives a witness '
                      'for every Neary normalized instance after its forced startup1 then0; '
                      'finite examples validate arithmetic but are not full Neary simulations.')


if __name__=='__main__':
    r=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
    print(r['status']);print([{k:s[k] for k in ('leading','operations','multiplications','additions','positive_unknowns','equations')} for s in r['sources']])
    print(r['startup']);print(r['full_outer_tuples']);print([{k:e[k] for k in ('beta','rows','erased_row','false_erasure','outer')} for e in r['examples']])
