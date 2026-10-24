#!/usr/bin/env python3
"""Independent literal, algebraic, degree, and finite Pell checks. Python stdlib only.

The unbounded reduction is PROOF.md, not these finite controls.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from math import gcd,isqrt
import copy,gzip,json,random
H=Path(__file__).resolve().parent

def need(cond,msg):
    if not cond:raise ValueError(msg)

def eval_rows(rows,env,mod=None):
    env=dict(env)
    for n,op,a,b in rows:
        aa=env[a] if isinstance(a,str) else a
        bb=env[b] if isinstance(b,str) else b
        v={'+':lambda:aa+bb,'-':lambda:aa-bb,'*':lambda:aa*bb}[op]()
        env[n]=v if mod is None else v%mod
    return env

def check_structure(c,p):
    need(c['domain']=='strictly positive integers','domain')
    need(c['witnesses']==p['witnesses']==['J','F','alpha','i','T','x','Y','n','eta','zeta'],'ten inputs')
    need(c['coefficient_binding']==p['coefficient_binding'],'whole original compact44 tuple')
    old={r[0]:r for r in p['source']};new={r[0]:r for r in c['source']}
    need(len(old)==105 and len(new)==len(c['source'])==96,'unique operation inventory')
    dropped={'I2','Dtau9','fb','U','ab','Po','sc','aXb','scab','4scab','Po2','Pe','Pe2','scaXb','64scaXb','qm1L','W','WBt','q4'}
    inserted={'DtauI','DtauI2','pair','omega','diff','diff2','fafc','fourfafc','LB','nVL'}
    need(set(new)==(set(old)-dropped)|inserted,'complete old/new gate sets')
    changed={
        'P1':['P1','*','q3','qbJ'],
        'Hn':['Hn','*','Hp','nVL'],
        'q3WBt':['q3WBt','*','q3','B'],
        'DpI2':['DpI2','*','Dp','DtauI2'],
        'HI':['HI','*','Hp','DtauI'],
        'fa':['fa','*','dM2','pair'],
        'N':['N','-','diff2','fourfafc']}
    for n in set(old)&set(new):need(new[n]==changed.get(n,old[n]),'retained or explicit modified gate '+n)
    explicit=[['DtauI','*','Dtau','I'],['DtauI2','*','DtauI','I'],
              ['pair','*','Dtau','Df'],['omega','-','fs','fc'],['diff','-','omega','fa'],
              ['diff2','*','diff','diff'],['fafc','*','fa','fc'],['fourfafc','*',4,'fafc'],['LB','*','L','B'],['nVL','-','nV','LB']]
    for row in explicit:need(new[row[0]]==row,'explicit inserted row '+row[0])
    deg={n:1 for n in c['witnesses']}|{n:0 for n in c['fixed_numerals']};used={'N'}
    for n,op,a,b in c['source']:
        need(n not in deg and op in '+-*','acyclic unique legal gate')
        da=deg[a] if isinstance(a,str) else 0;db=deg[b] if isinstance(b,str) else 0
        deg[n]=da+db if op=='*' else max(da,db)
    for n,op,a,b in reversed(c['source']):
        if n in used:used.update(x for x in (a,b) if isinstance(x,str))
    need(set(deg)<=used,'all gates, inputs, coefficient leaves live')
    need(dict(Counter(r[1] for r in c['source']))=={'*':57,'+':20,'-':19},'operation breakdown')
    need(deg==c['register_degrees'] and deg['N']==288,'syntactic degree schedule')
    return deg

# Sparse exact polynomial arithmetic. An exponent tuple is the monomial key.
def pc(v,d):return {(0,)*d:v} if v else {}
def pv(i,d):return {tuple(int(j==i) for j in range(d)):1}
def pa(a,b):
    out=dict(a)
    for k,v in b.items():out[k]=out.get(k,0)+v
    return {k:v for k,v in out.items() if v}
def pn(a):return {k:-v for k,v in a.items()}
def ps(a,b):return pa(a,pn(b))
def pm(a,b):
    out={}
    for x,c in a.items():
        for y,d in b.items():
            z=tuple(i+j for i,j in zip(x,y));out[z]=out.get(z,0)+c*d
    return {k:v for k,v in out.items() if v}
def pp(a,n):
    d=len(next(iter(a)))
    ans=pc(1,d)
    for _ in range(n):ans=pm(ans,a)
    return ans

def algebra():
    z,a,b=[pv(i,3) for i in range(3)]
    left=ps(pp(ps(ps(pp(z,2),pp(a,2)),pp(b,2)),2),pm(pc(4,3),pm(pp(a,2),pp(b,2))))
    right=pc(1,3)
    for ea in [-1,1]:
        for eb in [-1,1]:right=pm(right,ps(ps(z,pm(pc(ea,3),a)),pm(pc(eb,3),b)))
    need(left==right,'all coefficients of four-conjugate norm')
    Q,M,V,Z0=[pv(i,4) for i in range(4)];one=pc(1,4);delta=ps(Q,one)
    z=pa(pm(M,V),Z0)
    omega=ps(pm(delta,pp(z,2)),pm(pp(M,2),ps(pm(Q,pp(V,2)),one)))
    expected=ps(pa(pm(delta,pp(Z0,2)),pm(pc(2,4),pm(delta,pm(M,pm(V,Z0))))),pm(pp(M,2),ps(pp(V,2),one)))
    need(omega==expected,'all coefficients of centered cancellation')
    return {'norm_monomials':len(left),'centered_monomials':len(omega)}

def formulas(e):
    J,F,alpha,i,T,x,Y,n,eta,zeta=[e[v] for v in ['J','F','alpha','i','T','x','Y','n','eta','zeta']]
    beta,K0,MC,MF=[e[v] for v in ['beta','K0','MC','MF']]
    q=beta*J+1;X=q+x;mu=q*q+1;A=mu*Y*(X+1)+1;Delta=A*A-1;h=4*A-5
    k=eta+zeta;c=k*Y+eta;vfirst=X*mu*mu*Y*Y;D=vfirst*(vfirst+1)*k*k+1
    G=(q-1)*(q-F)+alpha;R=G*(q*q-1)+(MC+q*MF)*J;eidx=k-R-1
    C=q-F-alpha;B=(q*K0+X)*C-q*F;E=i*c*c;Fs=1+Delta*D*E*E
    Q=Delta*Delta*D*E*E;d=Q-1;b=c*(T+alpha)-R;V=Fs*b-c;Dn=Q*V*V-1
    L=h*D*E+b;W=1+q*(q-1)*L;P=q**4*(q-1);M=P*mu*mu*h;K=X*(3*c-2*X)+2
    Z=P*mu*mu*(h*(n+V)+K)+h*(mu*mu*(q*(q-1)*Y-q**3*W*B-(q-1)*X)-P*eidx)
    a=D*Fs;s=d*Z*Z;u=d*M*M*a;v=M*M*Dn;N=(s-v-u)**2-4*u*v
    center=n+V+Fraction(K,h)+Fraction(Y,q**3)-Fraction(W*B,q*(q-1))-Fraction(X,q**4)-Fraction(eidx,mu*mu)
    need(Fraction(Z,M)==center,'exact rational center')
    return {'q':q,'X':X,'Dp':Delta,'Hp':h,'Dtau':D,'I':E,'Df':Fs,'Q':Q,'V':V,'L':L,'W':W,'Mtot':M,'Znum':Z,'N':N}

def leading_values(c,ports):
    # Each pair stores a proved degree upper bound and its homogeneous part's
    # evaluation at the chosen point. A nonzero evaluation certifies attainment.
    checks=[]
    for prime in [1000000007,1000000009,998244353]:
        env={x:(1,1) for x in c['witnesses']}|{x:(0,ports[x]%prime) for x in c['fixed_numerals']}
        for name,op,a,b in c['source']:
            da,aa=env[a] if isinstance(a,str) else (0,a%prime)
            db,bb=env[b] if isinstance(b,str) else (0,b%prime)
            if op=='*':v=(da+db,aa*bb%prime)
            else:
                dd=max(da,db);v=(dd,((aa if da==dd else 0)+(1 if op=='+' else -1)*(bb if db==dd else 0))%prime)
            env[name]=v
        # Independently use the centered exact identity, not the raw N bound.
        def v(x):return env[x][1]
        z0=-v('Hp')*v('mu2')*v('q3')*(v('qbJ')*v('L'))*v('B')%prime
        omega=2*v('Q')*v('Mtot')*v('V')*z0%prime
        q=ports['beta']%prime;X=(q+1)%prime;k=2
        B=((q*ports['K0']+X)*(q-2)-q)%prime
        explicit=(2**7*pow(q,63,prime)*pow(X,15,prime)*pow(k,16,prime)*B*(q-1))%prime
        need(omega==explicit and omega!=0,'nonzero complete leading homogeneous form')
        checks.append({'prime':prime,'omega_degree':133,'omega_value':omega,'degree_266_value':omega*omega%prime})
    need(max(2*133,133+118,2*118,118+144)==266,'centered exact degree')
    return checks

def pell(A,n):
    x,y=1,0
    for _ in range(n):x,y=A*x+(A*A-1)*y,x+A*y
    return x,y

def finite_pell():
    output=[]
    for A in [2,3,4]:
        c=4*A*A-1
        for tau in [2,3]:
            modulus=tau*c*c;u,v=0,1
            for m in range(1,300001):
                u,v=v,(2*A*v-u)%modulus
                if u==0 and v==1:break
            else:raise ValueError('finite period control timeout')
            f,I=pell(A,m);need(I%modulus==0,'period divisibility')
            E=I//tau;D=tau*tau;Delta=A*A-1;Fs=1+Delta*D*E*E
            need(Fs==f*f and gcd(D,Fs)==1 and E%(c*c)==0,'coprime strong fusion')
            Q=Delta*Delta*I*I;delta=Q-1
            V=4*Q-3;y=4*Q-1
            need(Q*V*V-delta*y*y==1,'R=3 auxiliary norm control')
            need(V==Fs*(c-3)-c,'R=3 auxiliary congruence control')
            a=D*Fs
            for s1 in [-1,1]:
                for s2 in [-1,1]:
                    z=s1*tau*f+s2*y
                    need((delta*z*z-delta*a-(Q*V*V-1))**2-4*delta*a*(Q*V*V-1)==0,'all four signed fused zeros')
            need((delta*a-(Q*V*V-1))%D!=0,'root separation modulo D')
            output.append({'A':A,'tau':tau,'rank':3,'modulus':modulus,'period':m,'strong_ordinate_bits':I.bit_length()})
    return output

def expanded_transport(c):
    old=json.loads((H/'source/fusion98_equation.json').read_text())
    oldmap={r[0]:r for r in old['source']};newmap={r[0]:r for r in c['source']}
    removed={'qm1L','W','WBt','q4'}
    need(set(newmap)==(set(oldmap)-removed)|{'LB','nVL'},'whole 98-to-96 inventory')
    modified={'P1':['P1','*','q3','qbJ'],'Hn':['Hn','*','Hp','nVL'],'q3WBt':['q3WBt','*','q3','B']}
    for n in set(oldmap)&set(newmap):need(newmap[n]==modified.get(n,oldmap[n]),'98-to-96 retained gate '+n)
    for dead,consumer in {'qm1L':'W','W':'WBt','WBt':'q3WBt','q4':'P1'}.items():
        need([r[0] for r in old['source'] if dead in r[2:]]==[consumer],'whole private consumer '+dead)
    # Recursive free-cut expansion of the actual old/new carrier schedules.
    # Cut symbols are U,H,n,V,K,g,Y,S,B,L,D,e, with P=S*g.
    U,h,n,V,K,g,Y,S,B,L,D,e=[pv(i,12) for i in range(12)]
    P=pm(S,g);W=pa(pc(1,12),pm(g,L));nV=pa(n,V)
    zold=pa(pm(pm(P,U),pa(pm(h,nV),K)),pm(h,ps(pm(U,ps(ps(pm(g,Y),pm(S,pm(W,B))),D)),pm(P,e))))
    znew=pa(pm(pm(P,U),pa(pm(h,ps(nV,pm(L,B))),K)),pm(h,ps(pm(U,ps(ps(pm(g,Y),pm(S,B)),D)),pm(P,e))))
    need(c['fusion98_sha256']==sha256((H/'source/fusion98_equation.json').read_bytes()).hexdigest(),'frozen fusion98 hash')
    need(zold==znew,'all coefficients of expanded-transport carrier identity')
    rng=random.Random(960266)
    for _ in range(64):
        inputs={v:rng.randrange(-4,5) for v in c['witnesses']+c['fixed_numerals']}
        a=eval_rows(old['source'],inputs);b=eval_rows(c['source'],inputs)
        need(a['N']==b['N'] and a['Znum']==b['Znum'] and a['Mtot']==b['Mtot'],'signed complete-polynomial equality control')
    return {'old_operations':98,'new_operations':96,'exact_carrier_monomials':len(zold),'signed_controls':64,
            'frozen_98_sha256':sha256((H/'source/fusion98_equation.json').read_bytes()).hexdigest()}

def main():
    c=json.loads((H/'equation.json').read_text());p=json.loads((H/'source/parent_equation.json').read_text())
    need(sha256((H/'source/parent_equation.json').read_bytes()).hexdigest()==c['parent_sha256'],'exact pinned parent')
    deg=check_structure(c,p);rewrite=expanded_transport(c);ports={}
    for name,meta in c['coefficient_binding']['ports'].items():
        data=(H/'coefficients'/meta['file']).read_bytes();raw=gzip.decompress(data)
        need(sha256(data).hexdigest()==meta['gzip_sha256'] and sha256(raw).hexdigest()==meta['raw_sha256'],'whole coefficient '+name)
        ports[name]=int.from_bytes(raw,'little');need(ports[name].bit_length()==meta['bits'],'coefficient bit length')
    need(ports['beta']%2==1 and 0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'] and ports['K0']>0,'fixed-port box')
    algebra_results=algebra();rng=random.Random(26698)
    toy_ports={'beta':31,'K0':17,'MC':5,'MF':37}
    for j in range(24):
        e={k:rng.randrange(1,6) for k in c['witnesses']}|toy_ports
        expected=formulas(e);actual=eval_rows(c['source'],e)
        for name,value in expected.items():need(name=='W' or actual[name]==value,'independent formula control '+name)
    # Actual coherent payloads: every register against independent literal
    # graph under reduction. Avoid infeasible expanded giant coefficients.
    for prime in [1000000007,1000000009,998244353]:
        e={k:rng.randrange(1,6) for k in c['witnesses']}|{k:v%prime for k,v in ports.items()}
        actual=eval_rows(c['source'],e,prime);expected=formulas(e)
        need(all(n=='W' or actual[n]==v%prime for n,v in expected.items()),'actual payload modular control')
    degree=leading_values(c,ports);pell_results=finite_pell()
    mutations=[]
    for label,alter in [
        ('missing D factor',lambda x:x['source'].__setitem__(next(i for i,r in enumerate(x['source']) if r[0]=='DpI2'),['DpI2','*','Dp','I'])),
        ('old transport bound',lambda x:x['source'].__setitem__(next(i for i,r in enumerate(x['source']) if r[0]=='HI'),['HI','*','Hp','I'])),
        ('wrong fused factor',lambda x:x['source'].__setitem__(next(i for i,r in enumerate(x['source']) if r[0]=='pair'),['pair','*','Dtau','Dtau'])),
        ('wrong norm coefficient',lambda x:x['source'].__setitem__(next(i for i,r in enumerate(x['source']) if r[0]=='fourfafc'),['fourfafc','*',9,'fafc'])),
        ('wrong input domain',lambda x:x.__setitem__('domain','integers'))]:
        bad=copy.deepcopy(c);alter(bad)
        try:check_structure(bad,p)
        except ValueError:mutations.append(label)
        else:raise ValueError('mutation unexpectedly passed '+label)
    receipt={'status':'passed','ordinary_proof':'PROOF.md; inherited native calibration remains a dependency',
             'operations':96,'breakdown':{'*':57,'+':20,'-':19},'positive_variables':10,
             'exact_degree':266,'syntactic_degree':288,'identities':algebra_results,'expanded_transport':rewrite,
             'exact_toy_controls':24,'actual_payload_modular_controls':3,
             'degree_certificates':degree,'finite_pell_controls':pell_results,'mutations_rejected':mutations}
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
