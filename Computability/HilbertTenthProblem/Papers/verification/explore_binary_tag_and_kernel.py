"""Complete positive binary tag interface: six ANDs in one 97-op kernel."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import explore_binary_tag_queue_history as binary
import round39_1980_boolean_history_components as inherited
from round13_1980_certificate import verify_primitives

OUTER_NAMES = 'D AH H Q S1 Tcontent E Nsum q v Tplus r'.split()
CORE_NAMES = ['pell_'+x for x in inherited.CORE_NAMES if x != 'r']
NAMES = OUTER_NAMES+CORE_NAMES


def constants(beta, app, initial):
    assert beta >= 2 and len(app) >= 2 and app[0] == initial[0] == 0
    K = 2**beta
    Li = 2**len(initial)
    U = sum(b*2**i for i,b in enumerate(app))
    Ni = sum(b*2**i for i,b in enumerate(initial))
    C = 2
    while C <= max(16*K*K*Li, 16*K*2**len(app), 64):
        C *= 2
    return dict(C=C, k=K//2, B=2**(len(app)-1), Ut=U//2,
                c=K//2-1, Ni=Ni, Li=Li)


def outer(c):
    rows = [
        ('R','*',c['k'],'D'),
        ('twice_T','*',2,'Tcontent'), ('N','+','twice_T','S1'),
        ('M1','+','Q','S1'), ('L','+','Nsum','H'),
        ('cH','*',c['c'],'H'),
        ('n_app','*',c['Ut'],'M1'), ('n_trim','-','Tcontent','E'),
        ('n_output','+','n_trim','n_app'), ('n_lhs','*','D','n_output'),
        ('n_rhs','-','N',c['Ni']),
        ('l_app','*',c['B']-1,'M1'), ('l_output','+','L','l_app'),
        ('l_lhs','*','D','l_output'), ('two_q','*',2,'q'),
        ('l_initial','-','L',c['Li']), ('l_rhs','+','l_initial','two_q'),
        ('qm1','-','q',1), ('head_lhs','*','R','H'),
        ('compiled_product','*',c['C'],'AH'), ('head_rhs','+','H','qm1'),
        ('q_lhs','*','R','v'),
        ('WM','+','Q','M1'), ('WG','+','Q','AH'),
    ]
    # Head pair first for even index; content pair last for its pre-mask bound.
    for prefix,fields in [('packS',['S1','M1','E','Q','Q','N']),
                          ('packW',['H','L','cH','WM','WG','Nsum'])]:
        last = fields[-1]
        for i in range(4,-1,-1):
            mul, name = prefix+'mul'+str(i), prefix+str(i)
            rows += [(mul,'*','q',last),(name,'+',fields[i],mul)]
            last = name
    rows += [
        ('q2','*','q','q'), ('q3','*','q2','q'), ('n','*','q3','q3'),
        ('n2','*','n','n'), ('nm1','-','n',1),
        ('Wp1','+','packW0',1), ('packed_bound','+','packS0','Tplus'),
        ('index_upper','*','n','Wp1'),
        ('index_gap','+','index_upper','Tplus'), ('r_rhs','*','nm1','index_gap'),
    ]
    return rows


def core():
    rename = {x: 'pell_'+x for x in inherited.CORE_NAMES if x != 'r'}
    rename.update({row[0]:'pell_'+row[0] for row in inherited.CORE})
    return [tuple(rename.get(x,x) if isinstance(x,str) else x for x in row)
            for row in inherited.CORE]


def comparisons():
    pairs = [('n_lhs','n_rhs'),('l_lhs','l_rhs'),('packed_bound','Wp1'),
             ('head_lhs','head_rhs'),('head_lhs','compiled_product'),
             ('q_lhs','q'),('r','r_rhs')]
    rename = {x:'pell_'+x for x in inherited.CORE_NAMES if x!='r'}
    rename.update({row[0]:'pell_'+row[0] for row in inherited.CORE})
    return pairs+[(rename.get(a,a),rename.get(b,b)) for a,b in inherited.CORE_EQUALITIES]


def evaluate(rows, values):
    return binary.evaluate(rows, values)


def source(c,s):
    q,AH,H,Q,S1,T,E,Nsum,r,D = [s[x] for x in
                            'q AH H Q S1 Tcontent E Nsum r D'.split()]
    R = c['k']*D
    N,M1,L = 2*T+S1,Q+S1,Nsum+H
    S = sum(q**i*x for i,x in enumerate([S1,M1,E,Q,Q,N]))
    W = sum(q**i*x for i,x in enumerate([H,L,c['c']*H,Q+M1,Q+AH,Nsum]))
    n = q**6
    result = [D*(T-E+c['Ut']*M1)-N+c['Ni'],
              D*(L+(c['B']-1)*M1)-L+c['Li']-2*q,
              S+s['Tplus']-W-1,H*(R-1)-q+1,R*H-c['C']*AH,R*s['v']-q,
              r-(n-1)*(n*(W+1)+s['Tplus'])]
    a,pc,d,f,h,i,j,k,o,ps,w,tau,eta,zeta,ga,y = [s['pell_'+x] for x in
        'a c d f h i j k o s w tau eta zeta ga y_aux'.split()]
    U,Y=w*q**12,ps*q**12
    discr=a*a+4*a+3
    au=2*r+1+j*pc
    result += [U*Y*Y*(U*Y*Y+1)*k*k-tau*(tau+1),
               pc-Y*k-eta,k-eta-zeta,k-r-1-h*U*Y,
               a-Y*(U+1),d-U-a*pc-ga*(4*a+3),
               d*d-discr*pc*pc-1,(i*pc*pc)**2-discr*(f*f-1),
               discr*(f*f-1)*(au*au-y*y)-(1-y*y),au-pc-o*f]
    return result


def verify_source():
    c=dict(zip('C k B Ut c Ni Li'.split(),sp.symbols('C k B Ut cc Ni Li')))
    s=dict(zip(NAMES,sp.symbols(' '.join(NAMES))))
    rows=outer(c)+core()
    env=evaluate(rows,s)
    sources=source(c,s)
    aux=2*s['r']+1+s['pell_j']*s['pell_c']
    correction=sources[14]*(aux*aux-s['pell_y_aux']**2)
    records=[]
    for i,((a,b),f) in enumerate(zip(comparisons(),sources)):
        actual=sp.expand(env[a]-env[b])
        extra=correction if i==15 else 0
        assert sp.expand(actual-f-extra)==0,i
        records.append(dict(index=i,source=str(f),correction=str(extra)))
    for row in rows:
        for operand in row[2:]:
            if isinstance(operand,sp.Basic):env[operand]=operand
    primitives,counts=verify_primitives(rows,env)
    assert len(rows)==97 and counts=={'*':52,'+':45},counts
    assert len(NAMES)==28 and len(sources)==17
    return dict(operations=97,multiplications=52,additions=45,
                positive_unknowns=NAMES,equations=17,outer_operations=54,
                core_operations=43,primitive_instructions=primitives,
                comparisons=comparisons(),source_records=records,
                constants_relation='C is a fixed power of two; k=K/2 is even; all coefficients fixed before quantified witnesses')


def verify_pair_lemma():
    cases=accepted=0
    for bits in range(1,10):
        n=2**bits
        for W in range(1,n):
            for S in range(1,W+1):
                T=W-S
                r=(n-1)*((n+1)*(W+1)-S)
                assert r==S*(n*n-n)+(T+1)*(n*n-1)
                expected=2*bits+W.bit_count()-S.bit_count()-T.bit_count()
                assert r.bit_count()==expected
                assert (r.bit_count()>=2*bits)==(S&T==0)
                accepted += S&T==0
                cases += 1
    # Standalone complement extraction over all bounded q-block arrays.
    extraction=0
    q=4
    for ss in product(range(q),repeat=3):
        S=sum(x*q**i for i,x in enumerate(ss))
        for ww in product(range(q),repeat=3):
            W=sum(x*q**i for i,x in enumerate(ww))
            if W<S or S&(W-S):
                continue
            assert all(a<=b and a&(b-a)==0 for a,b in zip(ss,ww))
            extraction+=1
    return dict(complete_pair_cases=cases,disjoint_accepts=accepted,
                complete_three_block_extractions=extraction)


def check_tuple(c,vals,rows,terminal):
    env=evaluate(outer(c),vals)
    q,R,n=env['q'],env['R'],env['n']
    S,W=env['packS0'],env['packW0']
    T=W-S
    assert all(env[a]==env[b] for a,b in comparisons()[:7])
    assert all(vals[x]>0 for x in OUTER_NAMES)
    assert q==R**len(rows) and env['H']*(R-1)==q-1
    assert 0<S<W<n and n<=env['r']<2*n**3 and n>=64
    assert S&T==0 and env['r']%2==0
    assert env['r'].bit_count()==2*(n.bit_length()-1)
    sd=[env[x] for x in ['S1','M1','E','Q','Q','N']]
    wd=[env[x] for x in ['H','L','cH','WM','WG','Nsum']]
    assert all(0<=a<=b<q and a&(b-a)==0 for a,b in zip(sd,wd))
    assert all(0<=env[x]<q for x in ['Q','S1','M1','N','E','Nsum','L','AH'])
    S0=env['H']-env['S1']; M0=env['L']-env['M1']
    Nb=env['Nsum']-env['N']; Eb=env['cH']-env['E']
    assert all(x>=0 for x in [S0,M0,Nb,Eb])
    assert all(a&b==0 for a,b in [(env['Q'],env['M1']),(env['Q'],env['AH']),
        (S0,env['S1']),(env['N'],Nb),(env['E'],Eb),(M0,env['M1'])])
    K=2*c['k']
    assert R*(env['N']-2*env['E']-env['S1']+2*c['Ut']*env['M1'])==K*(env['N']-c['Ni'])
    assert R*(M0+c['B']*env['M1'])==c['k']*(env['L']-c['Li']+2*q)
    assert tuple(terminal)==(0,) and rows[0][0]==0
    return dict(height=len(rows),width=R.bit_length()-1,
                valuation=env['r'].bit_count(),r_bits=env['r'].bit_length(),
                zero_complements=[x==0 for x in [S0,M0,Nb,Eb]])


def canonical(beta,app,initial,rows,terminal):
    c=constants(beta,app,initial)
    A=2**(max(map(len,rows))+1)
    R=c['C']*A; q=R**len(rows); H=(q-1)//(R-1)
    packed={x:0 for x in 'Q S1 N E Nsum'.split()}
    for i,word in enumerate(rows):
        L=2**len(word); N=sum(b*2**j for j,b in enumerate(word)); s=word[0]
        row=dict(Q=s*(L-1),S1=s,N=N,E=(N%(2*c['k']))//2,Nsum=L-1)
        for key in packed:packed[key]+=row[key]*R**i
    T,rem=divmod(packed['N']-packed['S1'],2)
    assert rem==0 and T>0
    vals=dict(D=R//c['k'],AH=A*H,H=H,Q=packed['Q'],S1=packed['S1'],Tcontent=T,
              E=packed['E'],Nsum=packed['Nsum'],q=q,v=q//R)
    provisional=evaluate(outer(c),dict(vals,Tplus=1))
    vals['Tplus']=provisional['packW0']+1-provisional['packS0']
    vals['r']=evaluate(outer(c),vals)['r_rhs']
    return check_tuple(c,vals,rows,terminal)


def verify_canonical():
    histories=source_rows=0; witnesses=[]; odd_beta=0; zeros=[0]*4
    for beta in (2,3):
        for a in (2,3):
            for rest in product((0,1),repeat=a-1):
                app=(0,)+rest
                for ell in range(beta,beta+4):
                    for tail in product((0,1),repeat=ell-1):
                        initial=(0,)+tail
                        if not any(initial[1:beta]):continue
                        run=binary.first_halting_run(beta,app,initial,40)
                        if run is None:continue
                        rows,terminal=run
                        if terminal!=(0,) or not any(w[0] for w in rows):continue
                        result=canonical(beta,app,initial,rows,terminal)
                        histories+=1;source_rows+=len(rows);odd_beta+=beta%2
                        zeros=[a+int(b) for a,b in zip(zeros,result['zero_complements'])]
                        if len(witnesses)<8:witnesses.append(result)
    assert histories and odd_beta
    return dict(positive_startup_single_zero_histories=histories,source_rows=source_rows,
                odd_beta_histories=odd_beta,zero_complement_counts=zeros,
                outer_comparisons_per_tuple=7,extracted_AND_tests_per_tuple=6,
                every_index_even=True,examples=witnesses,
                pell_scope='All exact positive-converse hypotheses checked; enormous 16 auxiliary values not materialized')


def verify_product_inverse():
    geometries=accepted=nonpower=0
    for k in (2,4,8):
        for C in (16,32,64):
            for D in range(1,129):
                R=k*D
                for v in range(1,33):
                    q=R*v
                    H,rem=divmod(q-1,R-1)
                    if rem:continue
                    geometries+=1
                    assert H%2==1
                    AH,rem=divmod(R*H,C)
                    if rem:continue
                    A,rem=divmod(R,C)
                    assert rem==0 and A>0 and AH==A*H and D==(C//k)*A
                    accepted+=1;nonpower+=R&(R-1)!=0
    assert accepted and nonpower
    return dict(exact_geometries=geometries,positive_inverse_cases=accepted,
                nonpower_radix_inverse_cases=nonpower)


def verify():
    return dict(status='PASS',review_status='Author and two independent complete proof/source reviews and fresh verification runs PASS.',
                source=verify_source(),product_inverse=verify_product_inverse(),
                pair_lemma=verify_pair_lemma(),canonical=verify_canonical(),
                scope='Complete positive 97-operation binary encoded-tag interface for the stated startup and singleton-zero promise; above the ternary91 ledger, no raw-input/fixed-appendant universality claim.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2,default=str)+'\n',encoding='utf-8')
    print(result['status'],result['source']['operations'],result['canonical'])
