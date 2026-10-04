#!/usr/bin/env python3
"""New independent modular/Pell checks, not an upstream schedule evaluator.
Toy modular constants and exact subsystem fixtures do NOT claim compiler zeros.
The universal full-source result is the symbolic proof audited separately.
"""
import json,math,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent; OUT=ROOT/'audit_bootstrap'
def need(x,s):
    if not x: raise RuntimeError(s)
def pell(A,n):
    D=A*A-1; out=(1,0);base=(A,1)
    def mul(x,y):return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
    while n:
        if n&1:out=mul(out,base)
        n//=2
        if n:base=mul(base,base)
    return out

def primes(N):
    return [p for p in range(2,N+1) if all(p%d for d in range(2,math.isqrt(p)+1))]

counts={'factorial_prime_power_checks':0,'CRT_mask_cases':0,'outer_bound_checks':0}
for L in (15,20,25,32,40,64,80,128,256):
    t=math.factorial(L); a=(t&-t).bit_length()-1; m=t>>a
    need(a>=4 and pow(2,t,m)==1,'factorial odd-part property')
    for r in primes(L):
        if r==2:continue
        tt=t;v=0
        while tt%r==0:v+=1;tt//=r
        need(t%((r-1)*r**(v-1))==0,'totient divides factorial')
        counts['factorial_prime_power_checks']+=1
    for d in (5,25,125,625):
        if t%(1100*d):continue
        B=2**d; N=t//d
        need(N%1100==0,'exponent block')
        qmod=pow(2,t,t)
        # Computes J modulo t by exact division of a residue modulo (B-1)t.
        residue=pow(2,t,(B-1)*t)
        need((residue-1)%(B-1)==0,'repunit residue division')
        Jmod=((residue-1)//(B-1))%t
        need(Jmod%55==0 and pow(B,N,55)==1,'55 block')
        for MC in (2,6,10):
            for MF0 in (4,12):
                if max(MC,MF0)>=B-1:continue
                MF=MF0+B-1; Mmod=(MC+qmod*MF)*Jmod%t
                e0=Mmod%m
                es=[e0+j*m for j in range(4) if (e0+j*m)%4==3]
                need(len(es)==1,'unique exponent choice'); e=es[0]
                need(3<=e<4*m<=t//4,'small exponent')
                Z=(e-Mmod)%(1<<a)
                if Z==0:Z=1<<a
                need(1<=Z<=1<<a and Z%4==1,'positive residue Z')
                I=2*d+1; Wmod=pow(2,I,t); K=7; Cmod=(Wmod+Z)%t
                Fmod=(K+pow(2,e,t))*Cmod%t
                Rmod=((qmod*qmod-Z-qmod*Fmod)*(qmod*qmod-1)+Mmod)%t
                need(Rmod==e%t and Rmod%55==0 and Rmod%220==55,'full packed CRT')
                counts['CRT_mask_cases']+=1

for t in range(64,2049,4):
    need(2*t*t+2*t*2**(t//4)+4*t<2**t,'outer dominance')
    counts['outer_bound_checks']+=1

ratio=[]
for u in (1,5,9):
    p=55*u;n=40*u;X=2**p;Y=2**(33*u-1);E=X*Y
    a0=Y*(X+1);A=a0+2;D=A*A-1;H=4*a0+3;P=2*X*Y*Y+1
    main,c=pell(A,p);tau,firstpsi=pell(P,n);k=2*firstpsi
    eta=c-k*Y;zeta=k-eta
    need(eta>0 and zeta>0,'exact dyadic ratio')
    gamma=(main-a0*c-X)//H
    need((main-a0*c-X)%H==0 and gamma>0,'main projection')
    splits=[]
    for I in (3,5,7):
        mu,kappa=pell(A,I);W=2**I
        need((kappa-I)%D==0,'odd input delta')
        delta=(kappa-I)//D;rho=(mu-a0*kappa-W)//H;sigma=gamma-rho
        need((mu-a0*kappa-W)%H==0 and min(delta,rho,sigma)>0,'input split')
        need(main==X+a0*c+(rho+sigma)*H and mu==W+a0*kappa+rho*H,'shared literal roots')
        need(mu*mu-D*kappa*kappa==1,'input norm')
        splits.append(I)
    need((k-p-1)%E==25*u-1 and k>p+1,'nonintegral positive inverse')
    ratio.append({'u':u,'p':p,'n':n,'c_bits':c.bit_length(),'input_indices':splits,'remainder':25*u-1,'scope':'first/main/input subsystem; no literal packing/transport/full auxiliary tuple'})

aux=[]
for A,p in ((2,3),(3,3),(2,7)):
    D=A*A-1;c=pell(A,p)[1];m=2*c*p;f,v=pell(A,m)
    need(v%(c*c)==0,'normalized i');i=v//(c*c);S=D*v
    root,y=pell(S,p);need(root%S==0,'odd root quotient');V=root//S
    need((V+c)%f==0 and (V+p)%c==0,'auxiliary minus congruences')
    o=(V+c)//f;j=(V+p)//c
    need((o+p*f)%c==0,'T integrality');T=(o+p*f)//c
    need(min(i,S,V,y,o,j,T)>0,'positive auxiliary tuple')
    need(c*(T*f-1)-p*f*f==V,'literal T argument')
    need(f*f-D*(i*c*c)**2==1,'normalized strong')
    io=D*i
    need(1+(io*c*c)**2-D*(f*f-1)==1,'ordinary strong')
    need(S*S==D*D*(i*c*c)**2==D*(f*f-1),'same auxiliary coefficient')
    need(S*S*(V*V-y*y)+y*y==1,'auxiliary factor')
    aux.append({'A':A,'p':p,'m':m,'f_bits':f.bit_length(),'V_bits':V.bit_length(),'scope':'auxiliary/main/strong subsystem only; no source-scale or compiler claim'})

out={'status':'PASS','counts':counts,'exact_ratio_input_fixtures':ratio,'exact_auxiliary_fixtures':aux,'reviewed_full_draft_sha256':hashlib.sha256((ROOT/'FULL_COUNTERFAMILY.md').read_bytes()).hexdigest(),'scope':'Authored exact checks only. No upstream code or saved source schedule executed. No full astronomical tuple materialized. Full-source conclusion is the separate symbolic proof.'}
out['release_replay_attribution']='Author reran reviewer-written mathematical checks after CLI/path-only hardening; independent reviewer did not rerun these release bytes.'
out['replayed_full_draft_sha256']=out.pop('reviewed_full_draft_sha256')
out['original_independent_reviewed_sha256']='789e0d876393c4cd74076c41b9d030d3e192939346505217db13cfd599ed48a0'
import argparse
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--expect',type=Path,help='Byte-check this saved release replay receipt')
ap.add_argument('--output',type=Path,help='Create a new external receipt; packet/existing paths rejected')
args=ap.parse_args()
if args.output:
    target=args.output.resolve()
    if target.is_relative_to(ROOT):raise RuntimeError('Refusing output inside frozen packet')
    if target.exists():raise RuntimeError('Output must be a fresh external path')
    if args.expect and target==args.expect.resolve():raise RuntimeError('Output cannot overwrite expected receipt')
output=(json.dumps(out,indent=2)+'\n').encode()
if args.expect and args.expect.read_bytes()!=output:raise RuntimeError('Saved receipt byte mismatch')
if args.output:
    with args.output.open('xb') as f:f.write(output)
print(output.decode(),end='')
