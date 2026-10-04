"""New exact tests of the symbolic full-counterfamily proof's component identities.

This is not a saved-circuit interpreter, not a materialized full compiler zero,
and not a substitute for the infinite-domain proof in FULL_COUNTERFAMILY.md.
"""
from pathlib import Path
from math import factorial
import argparse,hashlib,json

ROOT=Path(__file__).resolve().parent
def require(v,label):
    if not v: raise RuntimeError(label)
def pell(A,n,mod=None):
    D=A*A-1; x,y=1,0; b,c=A,1
    while n:
        if n&1:
            x,y=x*b+D*y*c,x*c+y*b
            if mod: x%=mod;y%=mod
        b,c=b*b+D*c*c,2*b*c
        if mod:b%=mod;c%=mod
        n//=2
    return x,y
def v2(n): return (n&-n).bit_length()-1
def geometric_mod(B,N,M):
    # Exact division of the unique residue modulo (B-1)*M.
    q=pow(B,N,(B-1)*M)
    require((q-1)%(B-1)==0,'geometric division residue')
    return ((q-1)//(B-1))%M
def run():
    factorial_cases=crt_cases=block_cases=margin_cases=0
    for L in range(4,41):
        t=factorial(L); a=v2(t); m=t>>a
        require(pow(2,t,m)==1%m,'factorial odd-part theorem')
        factorial_cases+=1
        for d in [4,5,8,25]:
            if t%(1100*d) or a<4:continue
            B=1<<d;N=t//d
            for MC,MF0,K in [(2,4,17),(6,12,991),(10,12,2027)]:
                # Necessary-mask arithmetic fixtures only; not asserted valid programs.
                if MC>=B-1 or MF0>=B-1:continue
                MF=MF0+B-1
                qmod=pow(2,t,t);Jmod=geometric_mod(B,N,t)
                Mmod=((MC+qmod*MF)*Jmod)%t
                e0=Mmod%m
                choices=[e0+j*m for j in range(4) if(e0+j*m)%4==3]
                require(len(choices)==1,'unique exponent CRT')
                e=choices[0];require(3<=e<4*m<=t//4,'small exponent bound')
                Z=(e-Mmod)%(1<<a)
                if not Z:Z=1<<a
                require(1<=Z<=t and Z%4==1,'positive Z residue')
                I=2*d+1;W=1<<I;C=W+Z
                Fmod=(K+pow(2,e,t))*C%t
                Rmod=((qmod*qmod-Z-qmod*Fmod)*(qmod*qmod-1)+Mmod)%t
                require(Rmod==e,'literal packed R exponent residue')
                require(geometric_mod(B,N,55)==0,'J divisible55')
                require(pow(B,N,55)==1,'Q divisible55')
                crt_cases+=1

    # Exact materialized OUTER arithmetic only, using mock necessary-mask ports.
    # t values satisfy the proved modular premises but are not factorial outputs.
    outer=[]
    for d,t in [(4,17600),(5,88000),(8,35200),(25,880000)]:
        B=1<<d;N=t//d;a=v2(t);m=t>>a
        require(N%1100==0 and a>=4 and pow(2,t,m)==1%m,'outer fixture premises')
        q=1<<t;J=(q-1)//(B-1);Q=q*q-1
        MC=6;MF0=12;MF=MF0+B-1;K=991;I=2*d+1;W=1<<I
        M=(MC+q*MF)*J;e0=M%m;e=next(e0+j*m for j in range(4) if(e0+j*m)%4==3)
        Z=(e-M)%(1<<a) or(1<<a);C=W+Z;F=(K+(1<<e))*C
        alpha=q-F-2*Z-W-2*d
        R=(q*q-Z-q*F)*Q+M
        require(alpha>0 and F>0 and Z>0,'outer positive margins')
        require(R%55==0 and R%4==3 and R%t==e,'outer complete congruences')
        require((2*q-1)*Q<R<q**4-q**3,'literal scalar bounds')
        require(R>5*t+5,'scale margin')
        # Proven period t: reduce the huge exponent before modular powering.
        exponent=(R-t)%t
        require(exponent==e,'transport exponent reduction')
        require(((K+pow(2,exponent,q-1))*C+q-F-1)%(q-1)==0,'transport divisibility')
        # No w=2^(R-t) or Pell coordinate is materialized.
        outer.append(dict(d=d,t=t,e=e,Z=Z,R_bits=R.bit_length(),alpha_positive=True,
                          literal_packing_checked=True,transport_modulus_checked=True,
                          mock_ports=True,full_candidate=False))
        block_cases+=1

    for t in range(64,4097,4):
        # t/4 integer for exact small bound checks.
        require(2*t*t+2*t*(1<<(t//4))+4*t<(1<<t),'uniform outer bound')
        margin_cases+=1

    input_cases=0
    for A in range(3,34):
        a0=A-2;D=A*A-1;H=4*a0+3
        for I in range(3,22,2):
            p=I+4;mu,kappa=pell(A,I);main,c=pell(A,p)
            W=1<<I;X=1<<p
            require((kappa-I)%D==0 and(kappa-I)//D>0,'input delta')
            rho_num=mu-a0*kappa-W;gamma_num=main-a0*c-X
            require(rho_num%H==0 and gamma_num%H==0,'input projection divisibility')
            rho=rho_num//H;sigma=(gamma_num-rho_num)//H
            require(rho>0 and sigma>0,'shared input rho sigma positivity')
            require(mu==W+a0*kappa+rho*H,'literal input root')
            require(main==X+a0*c+(rho+sigma)*H,'literal main root')
            input_cases+=1

    auxiliary=[]
    for A,p in [(2,3),(3,3),(7,3),(2,7)]:
        D=A*A-1;c=pell(A,p)[1];m=2*c*p;f,y0=pell(A,m)
        require(y0%(c*c)==0,'normalized auxiliary i integrality')
        iN=y0//(c*c);S=D*y0
        root,y=pell(S,p);require(root%S==0,'odd auxiliary quotient')
        V=root//S;require((V+c)%f==0 and(V+p)%c==0,'minus congruences')
        o=(V+c)//f;j=(V+p)//c
        require((o+p*f)%c==0,'T integrality');T=(o+p*f)//c
        require(min(f,iN,S,y,V,o,j,T)>0,'all auxiliary positive')
        require(c*(T*f-1)-p*f*f==V,'literal quotient auxiliary V')
        require(f*f-D*(iN*c*c)**2==1,'normalized strong')
        require(D**2*(iN*c*c)**2*(V*V-y*y)+y*y==1,'normalized aux')
        iO=D*iN
        require(1+(iO*c*c)**2-D*(f*f-1)==1,'ordinary strong')
        require(D*(f*f-1)*(V*V-y*y)+y*y==1,'ordinary aux')
        auxiliary.append(dict(A=A,p=p,max_bits=max(f.bit_length(),y.bit_length(),V.bit_length()),
                              both_source_blocks_exact=True,full_candidate=False))

    return dict(status='PASS',scope='Exact component tests of full symbolic proof; no materialized full compiler zero',
        saved_schedule_executions=0,upstream_code_executions=0,factorial_oddpart_cases=factorial_cases,
        literal_CRT_cases=crt_cases,outer_arithmetic_fixtures=outer,uniform_margin_cases=margin_cases,
        input_shared_split_cases=input_cases,materialized_auxiliary_blocks=auxiliary,
        mathematical_claim='FULL_COUNTERFAMILY.md constructs every witness symbolically for arbitrary genuine compiler numerals',
        proof_sha256=hashlib.sha256((ROOT/'FULL_COUNTERFAMILY.md').read_bytes()).hexdigest())

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--expect',type=Path,help='Byte-compare canonical stdout with this saved receipt')
    ap.add_argument('--output',type=Path,help='Also create a new receipt outside this frozen packet')
    args=ap.parse_args()
    if args.output:
        target=args.output.resolve()
        require(not target.is_relative_to(ROOT),'Refusing output inside frozen packet')
        require(not target.exists(),'Output must be a fresh external path')
        if args.expect:require(target!=args.expect.resolve(),'Output cannot overwrite expected receipt')
    r=run();output=(json.dumps(r,indent=2)+'\n').encode()
    if args.expect:require(args.expect.read_bytes()==output,'Saved receipt byte mismatch')
    if args.output:
        with args.output.open('xb') as f:f.write(output)
    print(output.decode(),end='')
