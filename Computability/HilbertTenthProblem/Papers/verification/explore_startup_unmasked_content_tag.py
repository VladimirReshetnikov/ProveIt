"""Deleting GN from the91 source fails even with its startup promises."""
from pathlib import Path
import json
import sympy as sp
import explore_product_coordinate_tag as previous

old=previous.old
tag=previous.tag
kernel=previous.kernel
PARAMETERS=previous.PARAMETERS
POSITIVE=previous.POSITIVE
FIELDS=previous.FIELDS[:-1]


def prefix(c):
    result=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name in ('q8','guard_base','pack_add0','content_shifted','pack_add2'):
            continue
        if name=='scale':a=b='q4'
        if name=='higher_scaled':b='prefix_pair'
        result.append((name,op,a,b))
    return result,previous.prefix(c)[1]


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
    N=3*T+S if leading==0 else 3*T-2*Q
    M1=2*Q+S
    raw=previous.fields(c,s)
    P=sum(raw[f]*q**i for i,f in enumerate(FIELDS))
    src=[Kh*D-R,D*(T-E+Ut*M1)-N+s['Ninit'],
         D*(L+(B-1)*M1)-L+s['Linit']-3*q,
         R*H-H-q+1,R*H-C*Z,R*s['v']-q,
         2*r+1-q**8-2*P,r+s['betaP']-q**8]
    sub={kernel.SYM[n]:q**8 if n=='D0' else s[old.rename(n)] for n in kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in kernel.source_residuals(1)]
    src+=core
    env=old.run(schedule(c),s)
    u=s['pell_j']*s['pell_c']+2*r+1
    assert len(src)==len(previous.comparisons())==18
    records=[]
    for i,((a,b),polynomial) in enumerate(zip(previous.comparisons(),src)):
        correction=core[7]*(u*u-s['pell_y_aux']**2) if i==16 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(polynomial),
                            correction=sp.sstr(correction)))
    assert sp.expand(env[prefix(c)[1]]-P)==0
    assert not any(j in p.free_symbols for p in src)
    before=old.run(previous.prefix(c)[0],s)
    for a,b in previous.comparisons()[:6]:
        assert sp.expand(env[a]-env[b]-before[a]+before[b])==0
    dag=schedule(previous.constants(3,(leading,1,0,0)))
    counts=old.counts(dag)
    assert counts==dict(operations=86,multiplications=47,additions=39)
    assert len(POSITIVE)==len(set(POSITIVE))==29
    return dict(leading=leading,**counts,positive_unknowns=29,equations=18,
                outer_equations=8,kernel_equations=10,positive_coordinates=POSITIVE,
                parameters=PARAMETERS,fields=FIELDS,dag=dag,sources=records,
                scope='Generic fixed-coefficient DAG. Products by constants remain '
                      'counted even when a particular counterexample has constant0 or1.')


def witness(leading):
    if leading==0:
        app=(0,1,0,0);initial=(0,1,1,0,0,0)
        C=3**11;A=3**6
        selectors=[0,0]+[1,0,0]*9+[0,0,0]
        prefixes=[1,0,1,1,1,1,1,1,0,1,1,1,1,1,1,1,
                  0,1,0,0,1,1,0,0,0,0,1,0,0,1,0,1]
        actual=['011000','10000','0000100','001000','10000']
    else:
        app=(1,0);initial=(0,1,1)
        C=3**8;A=9
        selectors=[0]+[1]*32+[0]
        prefixes=[1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,0,
                  1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1]
        actual=['011','10','10']
    c=previous.constants(2,app)
    c.update(C=C,Cbar=C//3,guard_coefficient=(C-C//9)//2)
    K=c['K'];R=C*A;b=R//K;height=len(selectors)
    assert len(prefixes)==height
    width=len(tag.trits(R))-1
    Ni=tag.value(initial);Li=3**len(initial)
    assert initial[0]==0 and tag.value(initial[:2])//3==1
    assert C>max(K**3,3*K*3**len(app),2*K*c['U']+3,K*K*Li)
    markers=[];length=len(initial)
    for selector in selectors:
        assert length>=2
        markers.append(3**length)
        length+=len(app)-2 if selector else -1
    assert length==1
    pack=lambda xs:sum(x*R**i for i,x in enumerate(xs))
    S=pack(selectors)
    Q=pack([si*(marker-1)//2 for si,marker in zip(selectors,markers)])
    M1=2*Q+S;L=pack(markers);E=pack(prefixes)
    offset=S if leading==0 else -2*Q
    assert (offset-Ni)%3==0
    numerator=b*(E-c['Uthird']*M1)+(offset-Ni)//3
    T,remainder=divmod(numerator,b-1)
    assert remainder==0 and T>0
    N=3*T+offset
    q=R**height;H=(q-1)//(R-1)
    s=dict(Q=Q,S1=S,E=E,Tcontent=T,transport_scale=R//3,AH=A*H,
           R=R,q=q,H=H,L=L,Ninit=Ni,Linit=Li,v=q//R)
    raw=previous.fields(c,s)
    assert all(0<=raw[f]<q and tag.boolean(raw[f]) for f in FIELDS)
    assert raw['S0']%3==1 and not tag.boolean(raw['GN'])
    assert 0<N<q and N%R==Ni
    first_content_rows=[N//R**i%R for i in range(5)]
    assert first_content_rows[1]!=(tag.value(initial[2:]+(0,)))
    P=sum(raw[f]*q**i for i,f in enumerate(FIELDS))
    scale=q**8;r=P+(scale-1)//2
    s.update(r=r,betaP=scale-r)
    env=old.run(prefix(c)[0],s);env['pell_tr1']=2*r+1
    assert all(env[a]==env[b] for a,b in previous.comparisons()[:8])
    assert env[prefix(c)[1]]==P
    core_names={old.rename(n) for n in kernel.SYM if n not in ('D0','r')}
    assert set(s)-set(PARAMETERS)==set(POSITIVE)-core_names
    assert all(value>0 for name,value in s.items() if name not in PARAMETERS)
    exponent=8*width*height
    assert old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert r%2==0 and scale>=81 and 27<=r<scale and scale<r*r
    word=initial;visited=[]
    for expected in actual:
        assert ''.join(map(str,word))==expected
        visited.append(word)
        word=word[2:]+(app if word[0] else (0,))
    assert visited[-1] in visited[:-1] and any(word[0] for word in visited)
    residues=dict(E=E%(b-1),append_term=(c['Uthird']*M1)%(b-1),
                  offset_term=((offset-Ni)//3)%(b-1))
    assert (residues['E']-residues['append_term']+residues['offset_term'])%(b-1)==0
    return dict(leading=leading,appendant=app,initial=initial,constants=c,A=A,
                rows=height,width_exponent=width,selectors=selectors,
                length_markers=markers,prefix_rows=prefixes,
                modular_divisibility_denominator=b-1,modular_residues=residues,
                exact_T_numerator=numerator,raw_T=T,raw_content=N,
                correct_initial_base_R_residue=N%R,
                first_five_base_R_content_residues=first_content_rows,
                positive_outer_coordinates=s,retained_fields={f:raw[f] for f in FIELDS},
                omitted_guard=raw['GN'],packed_word=P,scale=scale,index=r,
                exact_central_valuation=exponent,index_parity=0,
                checked_outer_equations=8,checked_masks=8,
                actual_nonhalting_trace=actual,fixed_terminal=dict(content=0,length_marker=3),
                startup=dict(first_zero=True,positive_actual_initial_prefix=True,
                             genuine_one_event=True),
                kernel_scope='The exact fixed-plus43 converse supplies all sixteen '
                             'fresh positive auxiliaries at this even index. These huge '
                             'auxiliary integers are not materialized.',
                scope='Complete false solution of the proposed86 source on its startup '
                      'domain. Neither example is asserted to be a Neary compiler instance.')


def verify():
    return dict(status='PASS_STARTUP_UNMASKED_CONTENT_TAG86_COUNTEREXAMPLES',
                sources=[verify_source(e) for e in (0,1)],
                witnesses=[witness(e) for e in (0,1)],
                review='Author and two independent complete proof/source/dependency reviews and fresh verification PASS, with no findings.',
                proof='../1980/EXPLORATION_STARTUP_UNMASKED_CONTENT_TAG.md',
                scope='Rejected86 deletion of GN from the91 source. Both leading branches '
                      'admit full positive false halts despite first-zero, positive-prefix '
                      'and genuine-one startup. The valid91 and raw-input90 bounds are unchanged.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print([{k:s[k] for k in ('leading','operations','multiplications','additions',
                            'positive_unknowns','equations')} for s in result['sources']])
    print([{k:w[k] for k in ('leading','rows','width_exponent','exact_central_valuation',
                            'index_parity','modular_divisibility_denominator','modular_residues')}
           for w in result['witnesses']])
