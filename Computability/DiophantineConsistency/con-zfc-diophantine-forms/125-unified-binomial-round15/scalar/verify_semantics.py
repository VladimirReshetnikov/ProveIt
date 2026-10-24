#!/usr/bin/env python3
"""Finite controls for the new unbounded arithmetic proof; no upstream imports."""
from pathlib import Path
import argparse, gzip, hashlib, json, math, random
ROOT=Path(__file__).resolve().parent

def require(c,m):
    if not c: raise ValueError(m)

def vp(n,p):
    n=abs(n); require(n!=0,'valuation of zero');e=0
    while n%p==0:e+=1;n//=p
    return e

def pell(A,n,mod=None):
    D=A*A-1; out=(1,0);base=(A,1)
    def mul(x,y):
        a,b=x;c,d=y;z=(a*c+D*b*d,a*d+b*c)
        return tuple(v%mod for v in z) if mod else z
    while n:
        if n&1:out=mul(out,base)
        base=mul(base,base);n//=2
    return out

def payloads():
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text());ret={}
    for key,row in binding['payloads'].items():
        raw=gzip.decompress((ROOT/'coefficients'/row['file']).read_bytes());v=int.from_bytes(raw,'little')
        require(hashlib.sha256(raw).hexdigest()==row['raw_sha256'],key+' payload digest')
        require(v.bit_length()==row['bits'],key+' bitlength');ret[key]=v
    require(ret['beta']==(1<<1064921)-1,'beta recipe')
    require(ret['cone_A']==1<<1113 and ret['cone_B']==1<<666104,'cone recipes')
    return ret

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'SEMANTIC_CHECKS.json');args=ap.parse_args()
    p=payloads();rng=random.Random(1510464);count=0
    # Modular front-end laws use the actual fixed tuple.
    for modulus in (3,4,8,9,25,101):
        pp={k:v%modulus for k,v in p.items()}
        for _ in range(120):
            j,C,z,h,r,v,w,T,c,n,s=[rng.randrange(-100,101) for _ in range(11)]
            q=(pp['beta']*(6*j+1)+1)%modulus;W=(12*w+4)%modulus;X=q*W%modulus;Y=(2*v+1)*q**3%modulus
            a=(X+1)*Y%modulus;H=(4*a+3)%modulus;Delta=(a*a+H)%modulus
            F=((pp['K0']+W)*C-z*(q-1))%modulus
            R=((q*(q-F)-C)*(q*q-1)+(pp['MC']+q*pp['MF'])*(6*j+1))%modulus
            k=(R+1+h*X*Y)%modulus;eta=(c-Y*k)%modulus
            Derr=((pp['cone_A']*F-q)**2+(pp['cone_B']*C-q)**2)%modulus
            Budget=(k*k*(q*q-Derr)-4*q*q*eta*eta)%modulus
            ell=X*Y*Y%modulus;Dt=(1+ell*(ell+1)*k*k)%modulus;Df=(1+Delta*r*r*c**4)%modulus
            Q=Delta*Delta*r*r*c**4%modulus;delta=(Q-1)%modulus;V=(Df*(c-R+4*r*c*c*T)-c)%modulus;Cy=(Q*V*V-1)%modulus
            if modulus==3:require((q,X,a,H,Delta,Dt,Df,Q,delta,Cy)==(2,2,0,0,0,1,1,0,2,2),'mod-three separator')
            if modulus==4:require(Budget==0,'budget parity')
            K=(X*(3*c-2*X)+2)%modulus;Kquad=(X*(X+2*a*c)-1)%modulus
            require((2*Kquad-H*c*X+K)%modulus==0,'reduced projection identity');count+=1
    # The genuine composite supported modulus is larger in 2-adic order than I.
    A0,R,c,s,m0=2,3,15,2,180;f,I=pell(A0,m0);Delta=A0*A0-1
    require(I%(4*s*c*c)==0,'fixed strong divisibility');r=I//(c*c);M=16
    require(vp(I,2)==3 and vp(s*r,2)==4,'modulus beyond original strong scale')
    lam=4*m0*f;d=math.lcm(lam,4*I);rho=Delta*I;den=4*I*f*f
    residues=[]
    for h in range(M):
        nu=R+d*h
        # Compute the odd quotient chi_rho(nu)/rho modulo den*M, without gigantic exact Pell coordinates.
        x,_=pell(rho,nu,rho*den*M);require(x%rho==0,'odd quotient divisibility');V=x//rho
        numerator=(V+c-f*f*(c-R))%(den*M);require(numerator%den==0,'auxiliary T integrality')
        residues.append(numerator//den)
    require(sorted(residues)==list(range(M)),'supported-modulus surjectivity')
    for h1 in range(M):
        for h2 in range(h1):
            require(vp(residues[h1]-residues[h2],2)==vp(h1-h2,2),'supported isometry valuation')
    # Independently test Pell quotient derivative for both odd and even primes.
    valuations=0
    for rho in (2,3,4,5,6,9,10,12,15,18):
        primes=[p for p in (2,3,5) if rho%p==0]
        vals=[pell(rho,3+4*h)[0]//rho for h in range(13)]
        for i in range(13):
            for j in range(i):
                for p0 in primes:
                    require(vp(vals[i]-vals[j],p0)==vp(4*(i-j),p0),'Pell quotient lifting');valuations+=1
    # Intersectivity checks are diagnostic only, not the infinite proof.
    mods=list(range(1,501))+[2**e for e in range(1,11)]+[3**e for e in range(1,8)]+[19**e for e in range(1,4)]
    roots={}
    for modulus in mods:
        root=next((x for x in range(modulus) if ((x*x+3)*(x*x*x-19))%modulus==0),None)
        require(root is not None,'intersectivity control');roots[str(modulus)]=root
    # The unbounded inequality follows from positive slope 43 and endpoint margin 436.
    require(64*(24-9)-(21*24+20)==436,'powered projection endpoint')
    report={'status':'PASS','optimized_python':not __debug__,'actual_tuple_modular_checks':count,'pell_quotient_valuation_checks':valuations,'supported_modulus':{'A0':A0,'R':R,'c':c,'s':s,'strong_index':m0,'v2_I':3,'v2_sr':4,'M':M,'T_residues':residues},'intersective_moduli':len(roots),'coefficient_bits':sum(x.bit_length() for x in p.values()),'scope':'Finite arithmetic controls; the unbounded existence and consistency reductions are proved in PROOF.md, not inferred from tests.'}
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
