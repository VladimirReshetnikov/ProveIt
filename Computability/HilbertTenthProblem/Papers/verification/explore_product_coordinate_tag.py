"""Supply AH and recover an integer width from the retained geometry."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_compiled_initial_tag_bound as previous

old=previous.old
tag=previous.tag
kernel=previous.kernel
PARAMETERS=previous.PARAMETERS
FIELDS=previous.FIELDS
POSITIVE=[name for name in previous.POSITIVE if name!='A']+['transport_scale','AH']
constants=previous.constants


def prefix(c):
    rows=[]
    for name,op,a,b in previous.prefix(c)[0]:
        if name in ('transport_scale','AH','Rm1'):continue
        if name=='head_product':
            rows.extend([('head_product','*','R','H'),
                         ('compiled_product','*',c['C'],'AH'),
                         ('head_rhs','+','H','qm1')])
        else:rows.append((name,op,a,b))
    return rows,previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in kernel.schedule(1)]


def comparisons():
    result=[]
    for a,b in previous.comparisons():
        if a=='head_product':
            result.extend([('head_product','head_rhs'),('head_product','compiled_product')])
        else:result.append((a,b))
    return result


def fields(c,s):
    Q,S,T,E,H,L,Z=s['Q'],s['S1'],s['Tcontent'],s['E'],s['H'],s['L'],s['AH']
    N=3*T+S if c['leading']==0 else 3*T-2*Q
    M1=2*Q+S
    return dict(S0=H-S,S1=S,Q=Q,G=Q+Z,M0=L-M1,M1=M1,
                Ebar=c['c']*H-E,E=E,GN=N+c['guard_coefficient']*Z)


def verify_source(leading):
    s=dict(zip(POSITIVE+PARAMETERS,sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    C,Kh,Ut,B,cc,j=sp.symbols('C Khalf Uthird B c jguard')
    c=dict(C=C,Cbar=C/Kh,Khalf=Kh,Uthird=Ut,B=B,c=cc,K=3*Kh,
           U=3*Ut+leading,leading=leading,guard_coefficient=j)
    D,Z,Q,S,T,E,R,H,L,q,r=[s[n] for n in
                         ('transport_scale','AH','Q','S1','Tcontent','E','R','H','L','q','r')]
    N=3*T+S if leading==0 else 3*T-2*Q
    M1=2*Q+S
    raw=fields(c,s);P=sum(raw[f]*q**i for i,f in enumerate(FIELDS))
    src=[Kh*D-R,D*(T-E+Ut*M1)-N+s['Ninit'],
         D*(L+(B-1)*M1)-L+s['Linit']-3*q,
         R*H-H-q+1,R*H-C*Z,R*s['v']-q,
         2*r+1-q**9-2*P,r+s['betaP']-q**9]
    sub={kernel.SYM[n]:q**9 if n=='D0' else s[old.rename(n)] for n in kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in kernel.source_residuals(1)]
    src+=core
    env=old.run(schedule(c),s)
    u=s['pell_j']*s['pell_c']+2*r+1
    records=[]
    assert len(src)==len(comparisons())==18
    for i,((a,b),p) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(u*u-s['pell_y_aux']**2) if i==16 else 0
        assert sp.expand(env[a]-env[b]-p-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(p),correction=sp.sstr(correction)))
    assert sp.expand(env[prefix(c)[1]]-P)==0
    # Polynomial forward map from92, and the inverse under the two new
    # product identities. Integrality of inverse A is a separate theorem.
    A=sp.Symbol('A')
    forward={D:C/Kh*A,Z:A*H}
    prior={n:v for n,v in s.items() if n not in ('transport_scale','AH')}
    prior['A']=A
    before=old.run(previous.schedule(c),prior)
    for a,b in previous.comparisons():
        actual=env[a]-env['head_rhs'] if a=='head_product' else env[a]-env[b]
        assert sp.expand(actual.subs(forward,simultaneous=True)-(before[a]-before[b]))==0
    assert sp.expand((R*H-C*Z).subs(forward)-H*(R-C*A))==0
    dag=schedule(constants(3,(leading,1,0,0)))
    assert old.counts(dag)==dict(operations=91,multiplications=50,additions=41)
    assert len(POSITIVE)==len(set(POSITIVE))==29
    assert all('A' not in (n,a,b) for n,op,a,b in dag)
    assert all(n not in ('transport_scale','AH') for n,op,a,b in dag)
    return dict(leading=leading,operations=91,multiplications=50,additions=41,
                positive_unknowns=29,equations=18,outer_equations=8,kernel_equations=10,
                positive_coordinates=POSITIVE,parameters=PARAMETERS,fields=FIELDS,
                dag=dag,sources=records,
                scope='New product coordinates; the retained integer geometry gives a positive inverse A before the kernel.')


def integer_recovery():
    cases=accepted=small=nonpower=accepted_nonpower=0
    for beta,extra in product((2,3,4),(1,3,6)):
        k=3**(beta-1);C=3**(beta+extra)
        for D,w in product((1,2,3,C//k-1,C//k,2*C//k,3*C//k),(0,1,2,7)):
            R=k*D;H=1+R*w;q=R*H-H+1
            assert q%R==0 and R%3==q%3==0 and H%3==1
            Z=Fraction(R*H,C)
            assert (Z.denominator==1)==(R%C==0)
            np=sum(tag.trits(R))!=1 or sum(tag.trits(q))!=1
            cases+=1;small+=R<C;nonpower+=np
            if Z.denominator==1:
                A=R//C
                assert A>=1 and D==C//k*A and Z==A*H
                accepted+=1;accepted_nonpower+=np
    assert accepted_nonpower>0
    return dict(integer_geometry_cases=cases,integral_product_cases=accepted,
                R_below_C_rejections=small,nonpower_R_or_q=nonpower,
                integral_nonpower_geometries=accepted_nonpower,
                scope='Exact geometry-only integer recovery without power or mask premises. '
                      'Integral examples with nonpower R or q show the kernel is not being assumed.')


def power_recovery():
    cases=accepted=0
    for ce,m,t in product(range(1,7),range(1,9),range(1,5)):
        C=3**ce;R=3**m;q=R**t;H=(q-1)//(R-1)
        assert H%3==1
        Z=Fraction(R*H,C);cases+=1
        assert (Z.denominator==1)==(m>=ce)
        if Z.denominator==1:
            A=R//C
            assert A>=1 and Z==A*H
            accepted+=1
    return dict(power_geometry_cases=cases,integral_product_cases=accepted,
                scope='Integrality of CZ=RH forces C|R because H is prime to3.')


def outer_pair(c,initial,words,selectors,prefixes,final):
    beta=len(tag.trits(c['K']))-1;h=beta-1;Li=3**len(initial)
    assert beta>=2 and c['B']>=3
    assert c['K']**2*Li<c['C'] and initial[0]==0 and final==(0,)
    ce=len(tag.trits(c['C']))-1
    m=max(ce+2+max(map(len,[initial]+words)),2*h+3)
    if m%2==0:m+=1
    R=3**m;A=R//c['C'];t=len(words);q0=R**t
    pack=lambda vs:sum(v*R**i for i,v in enumerate(vs))
    S=pack(selectors);Q=pack([si*(3**len(w)-1)//2 for si,w in zip(selectors,words)])
    E=pack([(d-si)//3 for d,si in zip(prefixes,selectors)])
    N=pack([tag.value(w) for w in words]);L0=pack([3**len(w) for w in words])
    T=(N-S)//3 if c['leading']==0 else (N+2*Q)//3
    assert min(Q,S,E,T)>0
    result=[]
    for padded in (False,True):
        height=t+(m-h if padded else 0);q=R**height;H=(q-1)//(R-1)
        delta=q0*3*sum((R//c['Khalf'])**i for i in range(m)) if padded else 0
        s=dict(Q=Q,S1=S,E=E,Tcontent=T,transport_scale=R//c['Khalf'],AH=A*H,
               R=R,q=q,H=H,L=L0+delta,Ninit=tag.value(initial),Linit=Li,v=q//R)
        raw=fields(c,s)
        assert all(0<=raw[f]<q and tag.boolean(raw[f]) for f in FIELDS)
        assert raw['S0']%3==1
        P=sum(raw[f]*q**i for i,f in enumerate(FIELDS));D0=q**9;r=P+(D0-1)//2
        s.update(r=r,betaP=D0-r)
        env=old.run(prefix(c)[0],s);env['pell_tr1']=2*r+1
        assert all(env[a]==env[b] for a,b in comparisons()[:8])
        inverse={n:v for n,v in s.items() if n not in ('AH','transport_scale')}
        inverse['A']=R//c['C']
        before=old.run(previous.prefix(c)[0],inverse);before['pell_tr1']=2*r+1
        assert all(before[a]==before[b] for a,b in previous.comparisons()[:7])
        assert env[prefix(c)[1]]==before[previous.prefix(c)[1]]==P
        assert all(v>0 for n,v in s.items() if n not in PARAMETERS)
        assert old.unit.mask_expected(r,9*m*height) and old.unit.valuation(r)==9*m*height
        assert 27<=r<D0 and D0<r*r
        result.append(dict(parity=r%2,height=height,valuation=9*m*height))
    assert result[0]['parity']!=result[1]['parity']
    return result


def histories():
    cases=rows=cutoff=missing=nonzero=odd=0;branches=[0,0];parities=[0,0]
    for beta in (2,3,4):
      for a in (3*beta-2,4*beta-3):
        ell=a-beta+1
        structured=[0]*ell;structured[1]=structured[beta]=1
        for app in ((0,)*a,(1,)+(0,)*(a-1),(0,1)+(0,)*(a-2)):
          c=constants(beta,app)
          for initial in sorted({tuple(structured),(0,)+(1,)*(ell-1)}):
            w=initial;words=[];ss=[];ds=[]
            for _ in range(80):
                if len(w)<beta:break
                words.append(w);ss.append(w[0]);ds.append(tag.value(w[:beta]))
                w=w[beta:]+(app if w[0] else (0,))
            if len(w)>=beta:cutoff+=1;continue
            if w!=(0,):nonzero+=1;continue
            if not any(ss) or tag.value(initial[:beta])//3==0:missing+=1;continue
            pair=outer_pair(c,initial,words,ss,ds,w)
            cases+=1;rows+=len(words);odd+=beta%2;branches[c['leading']]+=1
            parities[pair[0]['parity']]+=1
    assert cases and min(branches)>0 and min(parities)>0 and odd
    return dict(admitted_histories=cases,genuine_source_rows=rows,full_outer_tuples=2*cases,
                fixed_leading_branches=branches,canonical_index_parities=parities,
                selected_padded=parities[1],odd_beta_histories=odd,
                excluded_non_single_zero_terminal=nonzero,excluded_missing_startup=missing,
                cutoff_unclassified=cutoff,
                scope='Every tuple checks all8 new outer comparisons, all7 inverse92 outer comparisons, '
                      'all9 masks, positivity and unchanged exact index valuation. The positive43 '
                      'converse supplies the large auxiliary values; these are not materialized Neary simulators.')


def short_appendants():
    records=[]
    for beta,app_text,input_text in ((2,'01','011'),(3,'10','001100'),
                                     (2,'010','011'),(2,'100','0110')):
        app=tuple(map(int,app_text));initial=tuple(map(int,input_text))
        a=len(app);leading=app[0];c=constants(beta,app)
        C=27*c['C']
        c.update(C=C,Cbar=C//c['Khalf'],guard_coefficient=(C-C//c['K'])//2)
        w=initial;words=[];ss=[];ds=[]
        for _ in range(20):
            if len(w)<beta:break
            words.append(w);ss.append(w[0]);ds.append(tag.value(w[:beta]))
            w=w[beta:]+(app if w[0] else (0,))
        assert w==(0,) and any(ss) and tag.value(initial[:beta])//3>0
        pair=outer_pair(c,initial,words,ss,ds,w)
        records.append(dict(leading=leading,a=a,appendant=app,initial=initial,
                            genuine_rows=len(words),outer=pair))
    return dict(cases=4,full_outer_tuples=8,records=records,
                scope='Both branches at a=2 and a=3 on the same proved domain; '
                      'complete new and inverse92 outer checks and both parity witnesses.')


def verify():
    return dict(status='PASS_PRODUCT_COORDINATE_TAG91',
                sources=[verify_source(e) for e in (0,1)],
                integer_recovery=integer_recovery(),power_recovery=power_recovery(),
                histories=histories(),short_appendants=short_appendants(),
                proof='../1980/EXPLORATION_PRODUCT_COORDINATE_TAG.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs pass.',
                scope='Complete91 on the admitted K^2*Li<C domain, beta>=2,a>=2, with the '
                      'positive-startup, first-zero and single-zero terminal completeness promises. '
                      'Neary normalized encoded instances satisfy them; the raw-input universal bound is unchanged.')


if __name__=='__main__':
    r=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
    print(r['status']);print([{k:s[k] for k in ('leading','operations','multiplications','additions','positive_unknowns','equations')} for s in r['sources']])
    print(r['integer_recovery']);print(r['power_recovery']);print(r['histories']);print(r['short_appendants'])
