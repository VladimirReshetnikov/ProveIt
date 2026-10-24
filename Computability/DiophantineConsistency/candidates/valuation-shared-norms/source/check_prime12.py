#!/usr/bin/env python3
"""Producer-independent finite checks for the prime-separated twelve-variable forms.

No builder, DAG implementation, or norm implementation is imported. These
checks do not replace the unbounded mathematical proofs.
"""
from pathlib import Path
from collections import Counter
import argparse, gzip, hashlib, itertools, json, random


def require(test, message):
    if not test:
        raise ValueError(message)


def eval_dag(packet, values, coefficients, modulus):
    vals=[]
    for node in packet['nodes']:
        tag=node[0]
        if tag=='variable': value=values[node[1]]
        elif tag=='coefficient': value=coefficients[node[1]]
        elif tag=='integer': value=node[1]
        elif tag=='add': value=vals[node[1]]+vals[node[2]]
        elif tag=='sub': value=vals[node[1]]-vals[node[2]]
        elif tag=='mul': value=vals[node[1]]*vals[node[2]]
        else: raise ValueError('unknown operation '+tag)
        vals.append(value%modulus)
    return vals[packet['output']],vals


def formal_norm(center, radicands, modulus):
    """Multiply conjugates in the rank-32 square-root algebra, independently."""
    products=[1]*32
    for mask in range(1,32):
        bit=mask&-mask
        products[mask]=products[mask^bit]*radicands[bit.bit_length()-1]%modulus
    def mul(left,right):
        result={}
        for i,x in left.items():
            for j,y in right.items():
                mask=i^j
                result[mask]=(result.get(mask,0)+x*y*products[i&j])%modulus
        return {mask:value for mask,value in result.items() if value}
    result={0:center%modulus,1:-1,2:-1,4:-1,8:-1,16:-1}
    for bit in [4,16,2,8,1]:
        conjugate={mask:(-value if mask&bit else value)%modulus
                   for mask,value in result.items()}
        result=mul(result,conjugate)
        require(all(not(mask&bit) for mask in result),'conjugate cancellation')
    require(all(mask==0 for mask in result),'norm is scalar')
    return result.get(0,0)


def independent_front(x,p,m):
    j,C,z,h,r,v,w,T,c,n,t,s=(x[k] for k in
        ['j','C','z','h','r','v','w','T','c','n','t','s'])
    beta,K0,MC,MF,cone_A,cone_B=(p[k] for k in
        ['beta','K0','MC','MF','cone_A','cone_B'])
    J=(6*j+1)%m; q=(beta*J+1)%m; W0=(12*w+4)%m
    X=q*W0%m; Y=(2*v+1)*pow(q,3,m)%m; E=X*Y%m
    a=(E+Y)%m; H=(4*a+3)%m; Delta=(a*a+H)%m
    F=((K0+W0)*C-z*(q-1))%m
    R=((q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J)%m
    k=(R+1+h*E)%m; eta=(c-Y*k)%m; zeta=(k-eta)%m
    G=(cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)**2)%m
    P=(G*eta*zeta-(t*t-G-eta*zeta+1)**2)%m
    Dg=((3*P-4)*s*s+1)%m
    I=s*r*c*c%m; Df=(1+Delta*I*I)%m
    Q=Delta*Delta*I*I%m; delta=(Q-1)%m
    V=(Df*(c-R+4*I*T)-c)%m; Cy=(Q*V*V-1)%m
    ell=X*Y*Y%m; Dt=(1+ell*(ell+1)*k*k)%m
    Dm=(1+Delta*c*c)%m; b0=(X+a*c)%m
    u=(H*T-b0)%m
    A=(u**5+10*u**3*Dm+5*u*Dm**2+3*H**2*(u**3+3*u*Dm)
       -19*H**3*(u*u+Dm)-57*H**5)%m
    B=(5*u**4+10*u*u*Dm+Dm*Dm+3*H*H*(3*u*u+Dm)
       -38*H**3*u)%m
    S=I*pow(H,5,m)%m; center=(S*n-A)%m
    return {key:val for key,val in locals().items() if key in
            ['J','q','W0','X','Y','a','H','Delta','F','R','k','eta','zeta',
             'G','P','Dg','I','Df','Q','delta','V','Cy','Dt','Dm','b0','u',
             'A','B','S','center']}


def reference(x,p,m,variant):
    f=independent_front(x,p,m)
    S2=f['S']**2%m
    rad=[f['B']**2*f['Dm']%m,9*S2*f['Df']%m,
         81*S2*f['Dt']%m,729*S2*f['Dg']%m]
    if variant=='rational':
        require(f['delta']%m!=0,'denominator modulo test prime')
        rad.append(S2*f['Cy']*pow(f['delta'],-1,m)%m)
        return pow(f['delta'],16,m)*formal_norm(f['center'],rad,m)%m
    rad.append(S2*f['delta']*f['Cy']%m)
    return formal_norm(f['center'],rad,m)


def structure(packet):
    nodes=packet['nodes']; require(packet['output']==len(nodes)-1,'terminal output')
    counts=Counter(); degrees=[]
    vars_used=set(); ports_used=set()
    for i,node in enumerate(nodes):
        tag=node[0]
        require(tag in ['integer','variable','coefficient','add','sub','mul'],'allowed tag')
        if tag in ['add','sub','mul']:
            require(len(node)==3 and 0<=node[1]<i and 0<=node[2]<i,'topological order')
            counts[tag]+=1
            degrees.append(degrees[node[1]]+degrees[node[2]] if tag=='mul'
                           else max(degrees[node[1]],degrees[node[2]]))
        else:
            require(len(node)==2,'leaf arity');degrees.append(1 if tag=='variable' else 0)
            if tag=='integer':require(isinstance(node[1],int),'integer literal')
            if tag=='variable':vars_used.add(node[1])
            if tag=='coefficient':ports_used.add(node[1])
    reachable=set();stack=[packet['output']]
    while stack:
        i=stack.pop()
        if i in reachable:continue
        reachable.add(i)
        if nodes[i][0] in ['add','sub','mul']:stack.extend(nodes[i][1:])
    require(len(reachable)==len(nodes),'all registers live')
    require(vars_used==set(packet['variables']) and len(vars_used)==12,'twelve live coordinates')
    require(ports_used==set(['beta','K0','MC','MF','cone_A','cone_B']),'six coefficient leaves')
    require(dict(sorted(counts.items()))==packet['operation_counts'],'operation census')
    require(sum(counts.values())==packet['operations'],'operation total')
    require(degrees[-1]==packet['exact_degree'],'degree upper bound')
    cert=packet['degree_certificate']
    require(sum(cert['monomial'].values())==packet['exact_degree'],'leading monomial degree')
    return {'operations':sum(counts.values()),'counts':dict(counts),'upper_degree':degrees[-1],
            'register_degrees':{k:degrees[v] for k,v in packet['named_registers'].items()
                                if k in ['A','B','S','cn','center','Q','Cy','delta','V','Df','Dt','Dg']}}


def carrier_checks():
    # Exact expansion in Z[u,D,H], independent of factored producer.
    def add(a,b):
        c=dict(a)
        for k,v in b.items():c[k]=c.get(k,0)+v
        return {k:v for k,v in c.items() if v}
    def mul(a,b):
        c={}
        for x,v in a.items():
            for y,w in b.items():
                k=tuple(i+j for i,j in zip(x,y));c[k]=c.get(k,0)+v*w
        return {k:v for k,v in c.items() if v}
    def scale(a,n):return {k:v*n for k,v in a.items() if v*n}
    D={(0,1,0):1};u={(1,0,0):1};one={(0,0,0):1}
    def qm(a,b):return (add(mul(a[0],b[0]),mul(D,mul(a[1],b[1]))),
                        add(mul(a[0],b[1]),mul(a[1],b[0])))
    z=(u,one);z2=qm(z,z);z3=qm(z2,z)
    left=(add(z2[0],{(0,0,2):3}),z2[1])
    right=(add(z3[0],{(0,0,3):-19}),z3[1]);A,B=qm(left,right)
    expect_A={(5,0,0):1,(3,1,0):10,(1,2,0):5,(3,0,2):3,
              (1,1,2):9,(2,0,3):-19,(0,1,3):-19,(0,0,5):-57}
    expect_B={(4,0,0):5,(2,1,0):10,(0,2,0):1,(2,0,2):9,
              (0,1,2):3,(1,0,3):-38}
    require(A==expect_A and B==expect_B,'exact quintic quadratic remainder')
    # Independent exact specialization gives B=1 in F3 whenever u=D=1,H=0.
    require(sum(v*pow(0,k[2]) for k,v in B.items())%3==1,'B prime-three unit')
    for m in range(1,1201):
        require(any(((x*x+3)*(x*x*x-19))%m==0 for x in range(m)),
                'finite intersective control '+str(m))
    require(4*4+3==19 and (2*4)%19!=0,'prime19 simple quadratic root')
    require((1**3-19)%2==0 and 3%2==1,'prime2 simple cubic root')
    require((2+3*2**2+3*2**3-2)%3==0,'prime3 shifted root')
    t=2;mod=3
    for k in range(2,10):
        candidates=[t+a*mod for a in range(3)
                    if ((t+a*mod)+3*(t+a*mod)**2+3*(t+a*mod)**3-2)%(3*mod)==0]
        require(len(candidates)==1,'unique Hensel lift at3')
        t=candidates[0];mod*=3
        require(((1+3*t)**3-19)%(9*mod)==0,'lifted cubic root')
    return {'exact_A_terms':len(A),'exact_B_terms':len(B),'intersective_moduli':1200,
            'shifted_three_adic_lifts':8}


def prime_residue_checks():
    n=0;coeff={'beta':1,'K0':2,'MC':1,'MF':0,'cone_A':2,'cone_B':1}
    for v,c,r,s,T,k,R in itertools.product(range(3),repeat=7):
        # Some coordinates have no effect on these identities but remain in
        # the direct independent formulas to avoid relying on the builder.
        x={'j':0,'C':1,'z':2,'h':k,'r':r,'v':v,'w':R,'T':T,
           'c':c,'n':0,'t':1,'s':s}
        f=independent_front(x,coeff,3)
        for key,value in {'q':2,'W0':1,'X':2,'a':0,'H':0,'Delta':0,
                          'Dm':1,'Df':1,'Dt':1,'Q':0,'delta':2,'Cy':2,
                          'u':1,'B':1}.items():
            require(f[key]==value,'prime-three residue '+key)
        n+=1
    return {'complete_residue_fixtures':n}


def load_coefficients(base):
    b=json.loads((base/'coefficients/BINDING.json').read_text());p={};hashes={}
    for name,rec in b['payloads'].items():
        raw=gzip.decompress((base/'coefficients'/rec['file']).read_bytes())
        digest=hashlib.sha256(raw).hexdigest()
        require(digest==rec['raw_sha256'],'raw coefficient hash '+name)
        value=int.from_bytes(raw,'little')
        require(value.bit_length()==rec['bits'],'raw coefficient bit length '+name)
        p[name]=value;hashes[name]=digest
    require(p['beta']==(1<<1064921)-1,'fixed beta numeral')
    require(p['cone_A']==1<<1113 and p['cone_B']==1<<666104,'fixed cone numerals')
    return p,hashes


def check_packet(packet,coefficients):
    report=structure(packet);rng=random.Random(24002912);points=0;zeroslices=0
    for prime in [1000003,1000033,1000037]:
        ports={k:v%prime for k,v in coefficients.items()}
        for attempt in range(24):
            x={k:rng.randrange(prime) for k in packet['variables']}
            if independent_front(x,ports,prime)['delta']==0:continue
            actual,_=eval_dag(packet,x,ports,prime)
            require(actual==reference(x,ports,prime,packet['variant']),'independent conjugate product')
            points+=1
        for key in ['s','r','c']:
            for repeat in range(4):
                x={k:rng.randrange(prime) for k in packet['variables']};x[key]=0
                f=independent_front(x,ports,prime);actual,_=eval_dag(packet,x,ports,prime)
                expected=pow((f['A']**2-f['B']**2*f['Dm'])%prime,16,prime)
                require(actual==expected,'exact zero-multiplier specialization')
                zeroslices+=1
    # Ensure deliberate corruption is detected by an independent comparison.
    corrupted=json.loads(json.dumps(packet));changed=False
    for node in corrupted['nodes']:
        if node==['integer',19]:node[1]=20;changed=True;break
    require(changed,'deliberate carrier corruption target')
    caught=False;prime=1000003;ports={k:v%prime for k,v in coefficients.items()}
    for attempt in range(20):
        x={k:rng.randrange(prime) for k in packet['variables']}
        if independent_front(x,ports,prime)['delta']==0:continue
        actual,_=eval_dag(corrupted,x,ports,prime)
        if actual!=reference(x,ports,prime,packet['variant']):caught=True;break
    require(caught,'deliberate corrupted coefficient rejected')
    report.update(independent_norm_points=points,zero_multiplier_slices=zeroslices,
                  deliberate_corruption_rejected=True)
    return report


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source-root',type=Path,required=True)
    ap.add_argument('--equations',type=Path,default=Path(__file__).resolve().parent/'equations')
    ap.add_argument('--receipt',type=Path,required=True);args=ap.parse_args()
    coefficients,hashes=load_coefficients(args.source_root)
    receipt={'carrier':carrier_checks(),'prime_three':prime_residue_checks(),
             'coefficient_sha256':hashes,'equations':{}}
    for path in sorted(args.equations.glob('prime_separated12_*.json')):
        packet=json.loads(path.read_text())
        receipt['equations'][path.name]=check_packet(packet,coefficients)
    receipt['scope']='Finite identity/circuit controls only; see the ordinary unbounded mathematical proofs.'
    args.receipt.parent.mkdir(parents=True,exist_ok=True)
    args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
