#!/usr/bin/env python3
"""Independent finite artifact checks for the twelve-integer construction.

These checks verify formulas, circuit transcription, the exact degree upper
bound with a nonzero leading slice, and finite modular interpolation fixtures.
They do not search for, assume, or prove a ZFC refutation or consistency.
No producer module is imported; only Python's standard library is used.
"""
from pathlib import Path
from collections import Counter
from math import gcd, isqrt
import argparse
import gzip
import hashlib
import json
import random


def need(test,message):
    if not test:
        raise ValueError(message)


def pi(x):
    return (x*x+31)*(x*x*x+x+1)


def pell(A,n,modulus=None):
    """(chi_A(n),psi_A(n)) by an independently written unit power."""
    Delta=A*A-1
    def mul(u,v):
        pair=(u[0]*v[0]+Delta*u[1]*v[1],u[0]*v[1]+u[1]*v[0])
        return tuple(t%modulus for t in pair) if modulus else pair
    result=(1,0)
    base=(A,1)
    while n:
        if n&1:
            result=mul(result,base)
        n//=2
        if n:
            base=mul(base,base)
    return result


def crt_two(a,m,b,n):
    g=gcd(m,n)
    need((b-a)%g==0,'incompatible CRT input')
    reduced=n//g
    t=((b-a)//g*pow(m//g,-1,reduced))%reduced if reduced>1 else 0
    return (a+m*t)%(m*reduced),m*reduced


def interpolation_fixtures():
    counts={'fibers':0,'classes':0,'max_I_bits':0,'max_index_bits':0}
    for A,R,N in [(2,3,1),(2,3,2),(2,3,3),(4,3,1)]:
        c=pell(A,R)[1]
        modulus=4*N*c*c
        f0,I0=1,0
        chosen=None
        for n0 in range(1,20001):
            f0,I0=(A*f0+(A*A-1)*I0)%modulus,(f0+A*I0)%modulus
            if n0%2==0 and I0==0:
                chosen=n0
                break
        need(chosen is not None,'finite fixture index search failed')
        n0=chosen
        f,I=pell(A,n0)
        Delta=A*A-1
        need(I%modulus==0 and f*f-Delta*I*I==1,'strong fixture')
        need(I%2==0 and f%2==1 and gcd(f,I)==1,'fixture parity')
        need((c-R)%4==0,'fixture phase')
        lam=4*n0*f
        need((4*I)%gcd(lam,4*I*I)==0,'CRT compatibility divisor')
        need(pell(A,lam,f*f)==(1,0),'squared-modulus period')
        # Both tiny and very large residues must be realizable for this same I.
        classes=[0,1,-1,2,I//2,I//3+7,I-2]
        S0=Delta*I
        target_modulus=4*I*I*f*f
        for residue in classes:
            L,period=crt_two(R,lam,R-4*I*residue,4*I*I)
            if L==0:
                L+=period
            need(L>0 and L%4==3,'positive auxiliary odd index')
            # chi_S0(L) is enormous. Compute exactly modulo S0*M, so integer
            # division by S0 recovers the exact residue of chi_S0(L)/S0 modM.
            ch,ps=pell(S0,L,S0*target_modulus)
            need(ch%S0==0,'odd Chebyshev divisibility')
            V=ch//S0
            need((V+c)%(f*f)==0,'modulo f² auxiliary congruence')
            need((V+L)%(4*I*I)==0,'modulo4I² Chebyshev congruence')
            numerator=V+c-f*f*(c-R)
            denominator=4*I*f*f
            need(numerator%denominator==0,'interpolated T is integral')
            T=numerator//denominator
            need((T-residue)%I==0,'full residue class recovered')
            counts['classes']+=1
            counts['max_index_bits']=max(counts['max_index_bits'],L.bit_length())
        counts['fibers']+=1
        counts['max_I_bits']=max(counts['max_I_bits'],I.bit_length())
    return counts


def check_quintic():
    # Exact sparse coefficient checks in Q[u,D,H], and the positive formula.
    def add(a,b):
        d=dict(a)
        for k,v in b.items():
            d[k]=d.get(k,0)+v
            if not d[k]:del d[k]
        return d
    def mul(a,b):
        d={}
        for u,c in a.items():
            for v,e in b.items():
                k=tuple(x+y for x,y in zip(u,v));d[k]=d.get(k,0)+c*e
        return {k:v for k,v in d.items() if v}
    def scale(a,k):return {u:v*k for u,v in a.items() if v*k}
    def power(a,n):
        r={(0,0,0):1}
        for unused in range(n):r=mul(r,a)
        return r
    u={(1,0,0):1};D={(0,1,0):1};H={(0,0,1):1}
    one={(0,0,0):1}
    def qmul(a,b):return (add(mul(a[0],b[0]),mul(D,mul(a[1],b[1]))),
                          add(mul(a[0],b[1]),mul(a[1],b[0])))
    z=(u,one);z2=qmul(z,z);z3=qmul(z2,z)
    left=(add(z2[0],scale(power(H,2),31)),z2[1])
    right=(add(add(z3[0],mul(power(H,2),u)),power(H,3)),
           add(z3[1],power(H,2)))
    A,B=qmul(left,right)
    expected_A={(5,0,0):1,(3,1,0):10,(1,2,0):5,(3,0,2):32,
                (1,1,2):96,(2,0,3):1,(0,1,3):1,(1,0,4):31,(0,0,5):31}
    expected_B={(4,0,0):5,(2,1,0):10,(0,2,0):1,(2,0,2):96,
                (0,1,2):32,(1,0,3):2,(0,0,4):31}
    need(A==expected_A and B==expected_B,'quadratic remainder coefficients')
    positive=add(add(add(scale(power(u,4),5),scale(mul(power(u,2),D),10)),
                         power(D,2)),scale(mul(power(H,2),D),32))
    positive=add(positive,scale(mul(power(H,2),power(u,2)),95))
    positive=add(positive,mul(power(H,2),power(add(u,H),2)))
    positive=add(positive,scale(power(H,4),30))
    need(B==positive,'positive B identity')
    roots=[]
    for m in range(1,401):
        root=next((x for x in range(m) if pi(x)%m==0),None)
        need(root is not None,'intersective finite control '+str(m))
        roots.append(root)
    # Coefficient/discriminant checks are exact integer arithmetic.
    need(-4-27==-31,'cubic discriminant')
    need((3**3+3+1)%31==0 and (3*3**2+1)%31!=0,'ramified simple root')
    need((-31)%8==1,'2-adic root class')
    return {'quadratic_remainder_monomials':[len(A),len(B)],
            'positive_B_identity':True,'intersective_moduli':len(roots)}


def check_bounds():
    """Independent integer comparisons for the product-weight bounds."""
    rng=random.Random(588832)
    for unused in range(1000):
        Delta=rng.randrange(2,100)
        c=rng.choice([-1,1])*rng.randrange(1,20)
        s=rng.choice([-1,1])*rng.randrange(1,20)
        r=rng.choice([-1,1])*rng.randrange(1,20)
        T=rng.randrange(-100,101)
        R=rng.randrange(1,100)
        P=rng.randrange(2,100)
        ell=rng.randrange(-100,101)
        k=rng.randrange(-100,101)
        I=s*r*c*c
        Q=Delta*Delta*I*I
        Df=1+Delta*I*I
        V=Df*(c-R+4*I*T)-c
        Da=(Q-1)*(Q*V*V-1)
        Dt=1+ell*(ell+1)*k*k
        Dg=(3*P-4)*s*s+1
        bound=1+c*c+R+c*c*(s*s+r*r)*(T*T+1)
        need(bound>abs(c-R+4*I*T),'bound on auxiliary coefficient')
        need(Df*bound+c*c+1>=abs(V),'bound on auxiliary V')
        pairs=[(ell*ell+k*k+2,Dt),(Delta+I*I+3,Df),
               (Q*(Df*bound+c*c+1),Da)]
        for upper,radicand in pairs:
            need(upper>0 and upper*upper>=radicand,'individual radical bound')
        X=rng.choice([-1,1])*rng.randrange(64,200)
        Y=rng.choice([-1,1])*rng.randrange(4096,5000)
        a=(X+1)*Y;H=4*a+3;Delta=a*a+H
        Dm=1+Delta*c*c;u=H*T-X-a*c
        B=5*u**4+10*u*u*Dm+Dm*Dm+32*H*H*(3*u*u+Dm)+2*H**3*u+31*H**4
        K=T*T+c*c+1;bm=256*K*K;S=I*H**5
        need(3*abs(a)<abs(H) and abs(X)<abs(H),'homogeneous shape bounds')
        need(4*Dm<c*c*H*H,'normalized main square-root bound')
        need(B*B*Dm<bm*bm*S*S,'homogeneous first-radical bound')
    return {'integer_bound_assignments':1000,'homogeneous_bound_assignments':1000}


def formal_norm(center,radicands,p):
    """Independent product of all five sign conjugates in a rank32 algebra."""
    products=[1]*32
    for mask in range(1,32):
        bit=mask&-mask
        products[mask]=products[mask^bit]*radicands[bit.bit_length()-1]%p
    def mul(a,b):
        out={}
        for i,x in a.items():
            for j,y in b.items():
                k=i^j
                out[k]=(out.get(k,0)+x*y*products[i&j])%p
        return {k:v for k,v in out.items() if v}
    value={0:center%p}
    value.update({1<<i:p-1 for i in range(5)})
    for bit in [16,4,1,8,2]:
        conjugate={i:(-x if i&bit else x)%p for i,x in value.items()}
        value=mul(value,conjugate)
        need(all(not(i&bit) for i in value),'conjugation elimination')
    need(all(i==0 for i in value),'scalar norm')
    return value.get(0,0)


def reference(values,ports,p,variant):
    j,C,z,h,r,v,w,T,c,n,t,s=(values[k] for k in
        ['j','C','z','h','r','v','w','T','c','n','t','s'])
    beta,K0,MC,MF,cone_A,cone_B=(ports[k] for k in
        ['beta','K0','MC','MF','cone_A','cone_B'])
    J=(6*j+1)%p;q=(beta*J+1)%p;W0=(12*w+4)%p
    X=q*W0%p;Y=(2*v+1)*pow(q,3,p)%p;E=X*Y%p
    a=(E+Y)%p;H=(4*a+3)%p;Delta=(a*a+H)%p
    F=((K0+W0)*C-z*(q-1))%p
    R=((q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J)%p
    k=(R+1+h*E)%p;eta=(c-Y*k)%p;zeta=(k-eta)%p
    G=(cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)**2)%p
    Pair=(G*eta*zeta-(t*t-G-eta*zeta+1)**2)%p
    Dg=((3*Pair-4)*s*s+1)%p
    I=s*r*c*c%p;Df=(1+Delta*I*I)%p
    Q=Delta*Delta*I*I%p;delta=(Q-1)%p
    V=(Df*(c-R+4*I*T)-c)%p
    Da=delta*(Q*V*V-1)%p
    ell=X*Y*Y%p;Dt=(1+ell*(ell+1)*k*k)%p
    Dm=(1+Delta*c*c)%p;b0=(X+a*c)%p
    u=(H*T-b0)%p
    A=(u**5+10*u**3*Dm+5*u*Dm**2+32*H**2*(u**3+3*u*Dm)
       +H**3*(u*u+Dm)+31*H**4*u+31*H**5)%p
    B=(5*u**4+10*u*u*Dm+Dm*Dm+32*H*H*(3*u*u+Dm)
       +2*H**3*u+31*H**4)%p
    S=I*pow(H,5,p)%p
    if variant=='compact':
        L=(1+B*B*Dm+Dt+Df+Da+Dg*Dg)%p
    elif variant=='product':
        bound=1+c*c+R+c*c*(s*s+r*r)*(T*T+1)
        K=T*T+c*c+1
        w1=(512*K*K+1)%p
        ba=Q*(Df*bound+c*c+1)%p
        bf=(Delta+I*I+3)%p
        bt=(2+ell*ell+k*k)%p
        w2=w1*(2*ba+1)%p
        w3=w2*(2*bf+1)%p
        w4=w3*(2*bt+1)%p
    else:
        raise ValueError('unknown weight bound')
    A0=B*B*Dm%p
    if variant=='product':
        A1=S*S*w1*w1*Da%p
        A2=S*S*w2*w2*Df%p
        A3=S*S*w3*w3*Dt%p
        A4=S*S*w4*w4*Dg%p
    else:
        W=(2*L+1)%p
        A1=S*S*pow(W,2,p)*Da%p
        A2=S*S*pow(W,4,p)*Dg%p
        A3=S*S*pow(W,6,p)*Dt%p
        A4=S*S*pow(W,8,p)*Df%p
    center=(S*n-A)%p
    return formal_norm(center,[A0,A1,A2,A3,A4],p)


def eval_dag(packet,values,ports,p):
    out=[]
    for tag,*args in packet['nodes']:
        if tag=='integer':v=args[0]
        elif tag=='coefficient':v=ports[args[0]]
        elif tag=='variable':v=values[args[0]]
        elif tag=='add':v=out[args[0]]+out[args[1]]
        elif tag=='sub':v=out[args[0]]-out[args[1]]
        elif tag=='mul':v=out[args[0]]*out[args[1]]
        else:raise ValueError('unknown node')
        out.append(v%p)
    return out[packet['output']]


def leading_dag(packet,weights,ports,p):
    degree=[];lead=[]
    for tag,*args in packet['nodes']:
        if tag=='integer':degree.append(0);lead.append(args[0]%p)
        elif tag=='coefficient':degree.append(0);lead.append(ports[args[0]]%p)
        elif tag=='variable':degree.append(1);lead.append(weights[args[0]]%p)
        elif tag=='mul':
            i,j=args;degree.append(degree[i]+degree[j]);lead.append(lead[i]*lead[j]%p)
        else:
            i,j=args;d=max(degree[i],degree[j]);degree.append(d)
            v=(lead[i] if degree[i]==d else 0)
            v+=(1 if tag=='add' else -1)*(lead[j] if degree[j]==d else 0)
            lead.append(v%p)
    return degree,lead


def load_ports(root):
    binding=json.loads((root/'coefficients/BINDING.json').read_text())
    ports={}
    for name,record in binding['payloads'].items():
        raw=gzip.decompress((root/'coefficients'/record['file']).read_bytes())
        need(hashlib.sha256(raw).hexdigest()==record['raw_sha256'],'coefficient hash '+name)
        ports[name]=int.from_bytes(raw,'little')
    return ports


def circuit_checks(packet,ports):
    variant=packet['weight_bound_variant']
    need(variant in ['compact','product'],'specified weight bound')
    degree=16000 if variant=='compact' else 4832
    need(packet['exact_degree']==degree,'specified exact degree')
    need(0<ports['MC']<ports['beta']<ports['MF'],'fixed constant ordering for R positivity')
    variables=['j','C','z','h','r','v','w','T','c','n','t','s']
    need(packet['variables']==variables,'exact12 coordinate list')
    ops=Counter()
    for idx,node in enumerate(packet['nodes']):
        tag=node[0]
        if tag in ('add','sub','mul'):
            need(len(node)==3 and all(isinstance(k,int) and 0<=k<idx for k in node[1:]),'topological node')
            ops[tag]+=1
        else:
            need(tag in ('integer','variable','coefficient'),'polynomial-only leaves')
    live=set()
    def visit(i):
        if i in live:return
        live.add(i)
        node=packet['nodes'][i]
        if node[0] in ('add','sub','mul'):
            visit(node[1]);visit(node[2])
    visit(packet['output'])
    need(len(live)==len(packet['nodes']),'no dead graph nodes')
    need(set(n[1] for n in packet['nodes'] if n[0]=='variable')==set(variables),'all12 variables live')
    need(dict(sorted(ops.items()))==packet['operation_counts'],'live operation census')
    if variant=='compact':need(sum(ops.values())==223,'compact census223')
    else:need(sum(ops.values())==248,'product census248')
    rng=random.Random(3216024)
    checks=0;degree_receipts=[]
    for p in [1000000007,1000000009,2147483647]:
        smallports={k:v%p for k,v in ports.items()}
        for index in range(32):
            values={name:rng.randrange(p) for name in variables}
            if index<3:values[['s','r','c'][index]]=0
            got=eval_dag(packet,values,smallports,p)
            expected=reference(values,smallports,p,variant)
            need(got==expected,'independent full norm transcription')
            checks+=1
        weights={name:rng.randrange(1,p) for name in variables}
        degrees,leading=leading_dag(packet,weights,smallports,p)
        need(degrees[packet['output']]==degree,'stated degree upper bound')
        rad_degrees=[degrees[packet['named_registers']['A'+str(i)]] for i in range(5)]
        need(rad_degrees==([70,410,570,786,1000] if variant=='compact'
                          else [70,190,212,250,302]),'exact stated radicand bounds')
        q0=6*smallports['beta']*weights['j']%p
        a0=2*pow(q0,4,p)*12*weights['w']*weights['v']%p
        I0=weights['s']*weights['r']*weights['c']**2%p
        R0=-pow(q0,3,p)*(12*weights['w']*weights['C']-q0*weights['z'])%p
        b=(4*I0*weights['T']-R0)%p
        if variant=='compact':
            expected=pow(2,448,p)*pow(a0,1728,p)*pow(I0,1088,p)*pow(b,256,p)%p
        else:
            Y0=2*weights['v']*pow(q0,3,p)%p
            K0=(weights['T']**2+weights['c']**2)%p
            expected=(pow(3,16,p)*pow(2,704,p)*pow(a0,544,p)*pow(Y0,128,p)
                      *pow(I0,160,p)*pow(K0,64,p)*pow(weights['c'],64,p)
                      *pow(weights['s']**2+weights['r']**2,32,p)
                      *pow(weights['T'],64,p)*pow(weights['h'],64,p)
                      *pow(weights['s'],32,p))%p
        need(expected!=0 and leading[packet['output']]==expected,'nonzero stated-degree top slice')
        degree_receipts.append({'prime':p,'degree':degree,'radicand_degrees':rad_degrees,
                                'leading_slice':expected})
    # A changed literal numeral must be rejected by the independent formula.
    corrupted=json.loads(json.dumps(packet))
    for node in corrupted['nodes']:
        if node==['integer',31]:node[1]=32;break
    else:raise ValueError('literal31 absent')
    p=1000000007;smallports={k:v%p for k,v in ports.items()}
    rejected=False
    for unused in range(4):
        values={name:rng.randrange(p) for name in variables}
        if eval_dag(corrupted,values,smallports,p)!=reference(values,smallports,p,variant):
            rejected=True;break
    need(rejected,'quintic coefficient corruption was not detected')
    return {'variables':12,'operations':sum(ops.values()),'operation_counts':dict(ops),
            'full_circuit_modular_checks':checks,'leading_slices':degree_receipts,
            'changed31_rejected':rejected}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root',type=Path,required=True)
    parser.add_argument('--equation',type=Path,required=True)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    packet=json.loads(args.equation.read_text())
    receipt={'scope':'Finite artifact and modular interpolation checks; universal proofs are separate.',
             'equation_sha256':hashlib.sha256(args.equation.read_bytes()).hexdigest(),
             'quintic':check_quintic(),
             'bounds':check_bounds(),
             'interpolation':interpolation_fixtures(),
             'circuit':circuit_checks(packet,load_ports(args.source_root))}
    out=json.dumps(receipt,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(out)
    print(out)


if __name__=='__main__':main()
