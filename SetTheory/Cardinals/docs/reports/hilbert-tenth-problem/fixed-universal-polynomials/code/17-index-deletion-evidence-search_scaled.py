"""New authored, bounded first/main subsystem search, never a full-source test.

The asymptotic integer-root filter is a candidate generator only. Only exact
Pell checks certify returned fixtures. Missing: literal packed R, transport,
input, common rho split, and full auxiliary quotient equations.
"""
from pathlib import Path
import argparse,json,time
from sympy import integer_nthroot

def pell(a,n):
    # Independent quadratic-unit binary powering.
    D=a*a-1; x,y=1,0; b,c=a,1
    while n:
        if n&1: x,y=x*b+D*y*c,x*c+y*b
        b,c=b*b+D*c*c,2*b*c; n//=2
    return x,y

def run(maxp,modulus):
    started=time.time(); generated=0; filtered=0; tested=0; hits=[]
    for p in range(7,maxp+1,4):
        X=1<<p; N=(X+1)**(p-1)
        for d in range(3,p-1,2):
            n=(p+d)//2
            lower=N>>(d+p*(n-1))
            Y0=int(integer_nthroot(lower,d)[0]); generated+=1
            for Y in [Y0,Y0+1]:
                if Y<4096 or Y%modulus: continue
                filtered+=1
                A=Y*(X+1)+2; P=2*X*Y*Y+1
                D,c=pell(A,p); tau,k0=pell(P,n); k=2*k0; tested+=1
                eta=c-k*Y; zeta=k-eta; H=4*(A-2)+3
                if eta>0 and zeta>0 and (D-(A-2)*c-X)%H==0:
                    gamma=(D-(A-2)*c-X)//H
                    if gamma<=1: raise RuntimeError('Unexpected nonpositive gamma')
                    # Direct equation checks, not saved schedule interpretation.
                    if D*D-(A*A-1)*c*c !=1: raise RuntimeError('main norm')
                    if tau*tau-X*Y*Y*(X*Y*Y+1)*k*k!=1: raise RuntimeError('first norm')
                    hits.append(dict(p=p,n=n,defect=d,X=str(X),Y=str(Y),Y_v2=(Y&-Y).bit_length()-1,
                        gamma_positive=True,eta_positive=True,zeta_positive=True,
                        h_remainder=(k-p-1)%(X*Y),max_coordinate_bits=max(D.bit_length(),tau.bit_length()),
                        scale16_valid=(X%16==0 and Y%4096==0),
                        full_candidate=False))
                    print(json.dumps({'found':hits[-1]}),flush=True)
                    if modulus==4096: break
            if hits and modulus==4096: break
        if hits and modulus==4096: break
    return dict(max_p=maxp,filter_modulus=modulus,generated=generated,filtered=filtered,exact_tests=tested,
                hits=hits,elapsed_seconds=time.time()-started,scope='First/main norms, strict ratio, main projection only; no full candidate')

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--max-p',type=int,default=255); ap.add_argument('--modulus',type=int,default=4096)
    ap.add_argument('--output',type=Path,required=True); a=ap.parse_args()
    r=run(a.max_p,a.modulus); a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='hits'}))
