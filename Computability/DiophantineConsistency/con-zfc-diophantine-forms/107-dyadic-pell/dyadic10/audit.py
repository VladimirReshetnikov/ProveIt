#!/usr/bin/env python3
"""Finite checks for the dyadic, three-center circuit; universal claims are in PROOF.md.
The coefficient reader and circuit evaluator are adapted from the pinned upstream
p10-positive-scaled-norm package. This audit's formula and degree checks are new.
"""
from pathlib import Path
import sys,json,random,math,itertools,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE)); sys.dont_write_bytecode=True
import circuit,build

def require(condition,message):
    if not condition: raise RuntimeError(message)

def norm(s,a,b,c,d,p):
    sig1=(a+b+c)%p; sig2=(a*b+(a+b)*c)%p; sig3=a*b*c%p
    U=(s+d)%p; P=(U-sig1)%p; sd=s*d%p
    E=(P*P+4*(sd-sig2))%p
    G=(E*E+16*(sd*P*P-4*sig3*U))%p
    O=(E*P-16*sig3)%p
    return (G*G-64*sd*O*O)%p

def independent(env,p):
    beta,K0,MC,MF=[env[x] for x in circuit.FIXED]
    j,F,alpha,i,T,w,Y,n,eta,zeta=[env[x] for x in circuit.WITNESSES]
    J=(2*j+1)%p; q=(beta*J+1)%p; X=w*q%p
    C=(q-F-alpha)%p; k=(eta+zeta)%p; c=(k*Y+eta)%p; a=Y*(X+1)%p
    mu=(q*q+1)%p; lam=2*mu%p; Ap=(lam*(a+2)+1)%p
    Hp=(4*Ap-5)%p; Dp=(Ap*Ap-1)%p; ap=(Ap-2)%p
    V0=X*lam*lam*Y*Y%p; Dtau=(V0*(V0+1)*k*k+1)%p
    R=(((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J)%p
    e=(k-R-1)%p; Bt=((K0+w)*C-F)%p
    I=i*c*c%p; Df=(1+Dp*I*I)%p; Q=Dp*Dp*I*I%p; delta=(Q-1)%p
    Tp=(T+alpha)%p; V=(Df*(c*Tp-R)-c)%p
    Dnum=(Q*V*V-1)%p; Dmain=(Dp*c*c+1)%p
    Cf=Ap*I%p; Ct=V0*k%p; L=(k+F+1)*(Tp+6)%p; W=(1+(q-1)*L)%p
    P1=q**3*(q-1)%p; Mtot=P1*mu*mu*Hp%p
    Znum=(P1*mu*mu*(Hp*(n+V+2*Cf+4*Ct)+8*(X+ap*c))
          +Hp*(mu*mu*((q-1)*Y-q**3*W*Bt)-P1*e))%p
    fs=delta*Znum*Znum%p; fa=16*delta*Mtot*Mtot*Dtau%p
    fb=4*delta*Mtot*Mtot*Df%p; fc=Mtot*Mtot*Dnum%p
    fd=64*delta*(P1*mu*mu)**2*Dmain%p
    N=norm(fs,fa,fb,fc,fd,p)
    return locals()

def differences(values,p):
    row=values[:]; first=[]
    while row:
        first.append(row[0])
        row=[(y-x)%p for x,y in zip(row,row[1:])]
    degree=max(i for i,x in enumerate(first) if x)
    return degree,first[degree]*pow(math.factorial(degree)%p,-1,p)%p

def leader(direction,ports,p):
    j,F,al,i,T,w,Y,n,eta,zeta=[direction[x] for x in circuit.WITNESSES]
    q0=2*ports['beta']*j%p; k0=(eta+zeta)%p; c0=k0*Y%p
    lam0=2*q0*q0%p; A0=lam0*w*q0*Y%p; Delta0=A0*A0%p
    I0=i*c0*c0%p; Q0=Delta0*Delta0*I0*I0%p
    f20=Delta0*I0*I0%p; R0=q0**3*(q0-F)%p
    Vtop=-f20*R0%p; Cf0=A0*I0%p; Ct0=w*q0*lam0*lam0*Y*Y*k0%p
    M0=4*q0**8*A0%p; L0=(k0+F)*(T+al)%p; B0=w*(q0-F-al)%p
    z0=-L0*B0%p
    return pow(2,22,p)*pow(Q0,8,p)*pow(M0,16,p)*pow(Vtop,8,p)*pow(Cf0,4,p)*pow(Ct0,2,p)*z0*z0%p

def pell(A,n):
    x,y=1,0
    for _ in range(n): x,y=A*x+(A*A-1)*y,x+A*y
    return x,y

def main():
    started=time.time(); ports=build.load_ports(); packet=build.packet(); source=circuit.rows()
    rng=random.Random(20261023)
    results={'coefficient_hashes':True,'operations':packet['operations'],'operation_breakdown':packet['operation_breakdown']}
    p=(1<<127)-1; pm={k:v%p for k,v in ports.items()}
    keys=['q','C','X','a','k','c','mu','lam','Ap','Hp','Dp','V0','Dtau','R','e','Bt','I','Df','Q','delta','Tp','V','Dnum','Dmain','Cf','L','Mtot','Znum','fs','fa','fb','fc','fd','N']
    for z in range(100):
        env=dict(pm);env.update({x:rng.randrange(1,p) for x in circuit.WITNESSES})
        got=circuit.evaluate(source,env,mod=p); expect=independent(env,p)
        for x in keys:require(got[x]==expect[x],f'independent formula {x}, case {z}')
    results['independent_formula_points']=100
    degree_results=[]
    for p in ((1<<127)-1,(1<<89)-1):
        pm={k:v%p for k,v in ports.items()}
        for kind in ('diagonal','random_affine'):
            direction={x:1 if kind=='diagonal' else rng.randrange(1,p) for x in circuit.WITNESSES}
            intercept={x:0 if kind=='diagonal' else rng.randrange(1,p) for x in circuit.WITNESSES}
            values=[]
            for t in range(833):
                env=dict(pm);env.update({x:(direction[x]*t+intercept[x])%p for x in circuit.WITNESSES})
                values.append(circuit.evaluate(source,env,mod=p)['N'])
            degree,lc=differences(values,p)
            require(degree==706,f'expected degree706, got{degree}')
            require(lc==leader(direction,pm,p),'general exact leading form')
            if kind=='diagonal':
                q0=2*pm['beta']%p
                expected=9*pow(2,202,p)*pow(q0,366,p)*pow(q0-1,8,p)*(q0-2)**2%p
                require(lc==expected,'diagonal closed leading coefficient')
            degree_results.append({'prime_bits':p.bit_length(),'line':kind,'degree':degree,'leading_form_matches':True})
    results['degree_checks']=degree_results
    # Parity premises of the squareclass extraction, with extreme and mixed signs in V.
    parity_cases=0
    for z in range(150):
        beta=2*rng.randrange(8,100)+1
        env={'beta':beta,'K0':rng.randrange(1,100),'MC':rng.randrange(1,beta),'MF':rng.randrange(beta+1,2*beta)}
        env.update({x:rng.randrange(1,60) for x in circuit.WITNESSES})
        r=circuit.evaluate(source,env)
        for x in ('Dtau','Df','Dnum','delta','Dmain','Hp'):
            require(r[x]%2==1,'dyadic unit '+x)
        require(r['Dp']%2==0 and r['V0']%2==0,'even radicand parameters')
        require(r['delta']>0 and r['Dnum']>0,'positive auxiliary rational radicand')
        require(r['Hp']>32*env['Y'],'main projection upper bound')
        q=r['q']; al=env['alpha']; F=env['F']; mu=r['mu']; Dp=r['Dp']; k=r['k']; c=r['c']
        require(abs(r['R'])*1 < q**4+F*q**3+(al+2)*q*q,'global R majorant')
        require(abs(r['R']) < (F+al+1)*mu*mu,'R/mu² bound')
        require(c < k*Dp,'c/Delta < k')
        require(abs(r['e']) < (k+F+al+1)*mu*mu,'rho bound')
        require(r['L'] > k*r['Tp']+6*k+2*F+2*al+2,'transport weight majorant')
        parity_cases+=1
    results['parity_and_majorant_cases']=parity_cases
    gap_cases=0
    for S in range(2,45):
        for R in (5,7,9,11):
            x,y=pell(S,R);require(x%S==0,'odd Pell quotient')
            V=x//S;u=y-V;Q=S*S
            require(Q*V*V-(Q-1)*y*y==1,'auxiliary Pell identity')
            require(4*Q*u>V,'gap lower bound')
            require(u>3*S+1,'gap dominates canonical strong coordinates')
            gap_cases+=1
    results['canonical_gap_cases']=gap_cases
    results['elapsed_seconds']=round(time.time()-started,3)
    results['scope']='Finite exact and modular checks support the ordinary proof; not an end-to-end formal proof.'
    (HERE/'CHECKS.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()
