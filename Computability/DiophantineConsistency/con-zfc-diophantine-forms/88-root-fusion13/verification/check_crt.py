#!/usr/bin/env python3
"""Independent exact degree and arithmetic-transcription audit for CRT1088."""
from pathlib import Path
import json,random,sys,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from exact_polynomial import Ring
from check_integrated import coefficients,Fp,formal_conjugate_norm,evaluate_dag,require

def exact_degree():
    ring=Ring(['U','s','V','d','A','B','e','delta'])
    U,s,V,d,A,B,e,D=[ring.var(n) for n in ring.names]
    Z=U*V+s;Cn=U*U*((D+1)*V*V-1)
    J=[D*(Z*Z+d+e-A-B)-Cn,2*D*Z,2*D*Z,2*D]
    def multiply(left,right):
        out=[ring.scalar(0) for _ in range(4)]
        for i in range(4):
            for j in range(4):
                term=left[i]*right[j]
                if i&j&1:term=term*d
                if i&j&2:term=term*e
                out[i^j]=out[i^j]+term
        return out
    K=multiply(J,J)
    K[0]=K[0]-4*(D*D*A*B+D*Cn*(A+B))
    f=multiply(K,K)
    X2=[Z*Z+d+e,2*Z,2*Z,ring.scalar(2)]
    f=[value-64*D**3*A*B*Cn*X2[i] for i,value in enumerate(f)]
    weights=[6,11,19,22,26,34,42,22];offsets=[0,11,21,32]
    degrees=[[p.weighted_degree(weights)+offsets[i] for i,p in enumerate(parts)]
             for parts in (J,K,f)]
    require(degrees==[[64,58,68,54],[136,122,132,126],[272,258,268,262]],
            'CRT exact biquadratic component degrees')
    require(f[0].homogeneous(weights,272)=={(4,0,4,0,0,0,2,4):16},
            'CRT unique leading scalar')
    # The last two norms square this nonzero scalar leading part twice.
    lead=Ring(['j','w','v','h','r','c','z','C','beta'])
    j,w,v,h,r,c,z,C,beta=[lead.var(n) for n in lead.names]
    q0=6*beta*j;a0=12*w*v*q0**2;i0=2*r
    R0=q0**4*z-12*q0**3*w*C;k0=R0+h*a0;eta0=-q0*v*k0
    top=2**112*q0**64*a0**128*i0**64*c**128*R0**16*v**16*eta0**32
    monomial=(480,160,208,32,64,128,16,0,480)
    require(top.terms.get(monomial)==2**976*3**640, 'CRT selected leading coefficient')
    require(top.weighted_degree((1,1,1,1,1,1,1,1,0))==1088, 'CRT total degree')
    # Exact carrier identities, prior to all use of congruence reasoning.
    ring=Ring(['M','H','b','n','V','v','q'])
    M,H,b,n,V,v,q=[ring.var(k) for k in ring.names]
    Lcrt=4*H+1;U=M*H
    require(not (M*Lcrt-(4*U+M)).terms, 'CRT optimized scale identity')
    center=U*(n+V)+M*Lcrt*b+H*(v-q*q)
    require(not (center-(M*(H*(n+V)+Lcrt*b)+H*(v-q*q))).terms,
            'CRT carrier mod-M identity')
    require(not (center-(H*(M*(n+V)+v-q*q)+M*Lcrt*b)).terms,
            'CRT carrier mod-H identity')
    return {'degree':1088,'component_degrees':degrees,
      'cleared_F8_top':'16*delta^4*U^4*V^4*e^2',
      'full_norm_top':'2^16*Q0^16*Z0^16*e0^8',
      'selected_monomial':'j^480*w^160*v^208*h^32*r^64*c^128*z^16',
      'selected_coefficient':'2^976*3^640*beta^480',
      'leading_front_monomials':len(top.terms),
      'exact_CRT_carrier_identities':3}

def independent_front(inputs,ports,prime):
    x={n:Fp(v,prime) for n,v in inputs.items()}
    p={n:Fp(v,prime) for n,v in ports.items()}
    J=1+6*x['j'];q=1+p['beta']*J;W=4*(3*x['w']+1)
    X=W*q;Y=x['v']*q;a=(X+1)*Y;E=a-Y;H=4*a+3;Delta=(a+1)*(a+3)
    C=x['C'];F=p['K0']*C+W*C-x['z']*q+x['z'];alpha=q-C-F
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(p['MC']+p['MF']*q)*J
    k=R+1+x['h']*E;c=x['c'];eta=c-Y*k;zeta=(Y+1)*k-c
    I=(2*x['r']+1)*c*c;I2=I*I;Bstrong=Delta*I2
    Df=(a+2)**2*I2-I2+1;Q=(Delta*I)**2;delta=Q-1
    V=Df*c*x['T']-Df*R-c;Cy=(delta+1)*V*V-1
    ell0=X*Y*Y;L=ell0*k;Dtau=L*L+L*k+1;Dmain=1+Delta*c*c
    b0=a*c+X;coneU=p['cone_A']*F;coneZ=p['cone_B']*C
    G=coneU*coneZ-(coneU+coneZ-q)**2;Peta=eta*zeta
    Pair=G*Peta-(G+Peta-1-x['t']**2)**2
    Ag=x['v']*x['v']*Pair-(1+x['p2']**2+x['p3']**2+x['p3'])
    M=2*q*q;Lcrt=4*H+1;U=M*H;ML=M*Lcrt
    center=M*(H*(x['n']+V)+Lcrt*b0)+H*(x['v']-q*q)
    return {n:v.value for n,v in locals().copy().items() if isinstance(v,Fp)}

def transcription(packet,ports):
    rng=random.Random(1088);primes=(1000000007,1000000009,1000000033)
    checks=0;register_checks=0
    while checks<45:
        prime=primes[checks%3]
        inputs={name:rng.randrange(-30,31) for name in packet['variables']}
        if checks==0:inputs['v']=0
        if checks==1:inputs['c']=0
        if checks==2:inputs['v']=inputs['c']=0
        r=independent_front(inputs,ports,prime)
        if not r['delta']:continue
        values=evaluate_dag(packet,inputs,ports,prime)
        for name,value in r.items():
            if name in packet['named_registers']:
                require(values[packet['named_registers'][name]]==value,'CRT front register '+name)
                register_checks+=1
        dy=r['Cy']*pow(r['delta'],prime-2,prime)%prime
        radicands=[r['ML']**2*r['Dmain']%prime,r['U']**2*r['Df']%prime,
                   r['U']**2*r['Dtau']%prime,r['U']**2*r['Ag']%prime,
                   r['U']**2*dy%prime]
        expected=pow(r['delta'],16,prime)*formal_conjugate_norm(r['center'],radicands,prime)%prime
        require(values[packet['output']]==expected,'CRT complete formal-product diagnostic')
        checks+=1
    return {'actual_coefficient_modular_diagnostics':checks,'primes':list(primes),
            'independent_front_register_checks':register_checks,
            'exceptional_slices':['v=0','c=0','v=c=0']}

def main():
    start=time.monotonic()
    root=HERE.parent
    ports,binding_receipt=coefficients(root)
    packet=json.loads((root/'equations/norm13_crt_degree1088.json').read_text())
    receipt={'status':'PASS','fixed_coefficients':binding_receipt,
             'degree_certificate':exact_degree(),'arithmetic':transcription(packet,ports),
             'operations':packet['operations'],'variables':packet['variable_count'],
             'seconds':round(time.monotonic()-start,3),
             'scope':'Exact degree and arithmetic checks; ordinary semantic proof separately audited.'}
    (HERE/'CRT_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
