#!/usr/bin/env python3
"""Fresh finite checks of arithmetic specialization and boundary interfaces.
No upstream executable is imported. These corroborate the all-integer proofs.
"""
from pathlib import Path
from itertools import product
from math import comb, gcd, isqrt
import hashlib
import json

HERE=Path(__file__).resolve().parent

def pell(a,n):
    D=a*a-1
    def mul(p,q):return (p[0]*q[0]+D*p[1]*q[1],p[0]*q[1]+p[1]*q[0])
    out=(1,0);step=(a,1)
    while n:
        if n&1:out=mul(out,step)
        step=mul(step,step);n//=2
    return out

def quotient_pair(q):return (max(-q,0),max(q,0))

def power_tuple(b,e):
    k=e+1;out=b**e;w=max(b,k)
    a,auxy=pell(w+1,w);assert auxy%w==0
    g=auxy//w;x,y=pell(a,k)
    u,v=pell(a,2*k*y)
    assert gcd(u,4*y)==1
    beta=a+u*((1-a)*pow(u,-1,4*y)%(4*y))
    assert beta>1 and (beta-1)%(4*y)==0 and v%(y*y)==0
    s,t=pell(beta,k);M=2*a*b-b*b-1;m=b*out
    aq=quotient_pair((beta-a)//u)
    sq=quotient_pair((s-x)//u)
    tq=quotient_pair((t-k)//(4*y))
    rq=quotient_pair((x-y*(a-b)-m)//M)
    # Congruence divisions are verified, not rounded silently.
    assert beta-a==u*(aq[1]-aq[0])
    assert s-x==u*(sq[1]-sq[0])
    assert t-k==4*y*(tq[1]-tq[0])
    assert x-y*(a-b)-m==M*(rq[1]-rq[0])
    qb=(beta-1)//(4*y);qv=v//(y*y);strict=M-m
    natural=[w-b,w-k,y-k,*aq,*sq,*tq,*rq]
    positive=[out,a-1,beta-1,w,M,g,x,y,u,v,s,t,qb,qv,strict]+[n+1 for n in natural]
    assert len(positive)==26 and min(positive)>0 and min(natural)>=0
    residuals=[x*x-1-(a*a-1)*y*y,u*u-1-(a*a-1)*v*v,
        s*s-1-(beta*beta-1)*t*t,beta-1-4*y*qb,
        beta+u*aq[0]-a-u*aq[1],v-y*y*qv,
        s+u*sq[0]-x-u*sq[1],t+4*y*tq[0]-k-4*y*tq[1],
        y-k-natural[2],w-b-natural[0],w-k-natural[1],M-m-strict,
        a*a-1-((w+1)*(w+1)-1)*(w*g)*(w*g),
        2*a*b-M-b*b-1,x+M*rq[0]-y*(a-b)-m-M*rq[1]]
    assert len(residuals)==15 and not any(residuals)
    return {'base':b,'exponent':e,'positive_leaves':26,'equations':15,
        'largest_witness_bits':max(x.bit_length() for x in positive)}

def contained(mask,value):return mask&value==value

def spread(u,b,n,s):
    assert b>=2 and b&(b-1)==0 and 0<=u<b**n and s>=n+1
    cb=b**(s-1);end=cb**n
    copy=(end-1)//(cb-1);mask=(end*b**n-1)//(b*cb-1)
    assert (cb-1)*copy+1==end and (b*cb-1)*mask+1==end*b**n
    out=(u*copy)&((b-1)*mask)
    digits=[];v=u
    for i in range(n):digits.append(v%b);v//=b
    assert out==sum(x*b**(s*i) for i,x in enumerate(digits))
    return out

def pair(x,y):return (x+y)*(x+y+1)//2+y

def unpair(z):
    w=(isqrt(8*z+1)-1)//2;y=z-w*(w+1)//2
    return w-y,y

def main():
    # Inspect the exact inherited theorem bytes as data and check their pin.
    p=Path('/workspace/shared/sandpile-fixed-arity-independent-audit-20261004/pell-pinned-fetch.json')
    s=json.loads(p.read_text())['content']
    h=hashlib.sha256(s.encode()).hexdigest()
    assert h=='993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a'
    assert 'theorem matiyasevic {a k x y}' in s and 'theorem eq_pow_of_pell {m n k}' in s
    powers=[power_tuple(b,e) for b,e in [(b,0) for b in range(2,9)]+[(2,1),(3,1)]]
    nsub=nconstruct=0
    for M in range(128):
        R=2**(M+1);expansion=(R+1)**M
        for V in range(140):
            slot=R**V;head,rem=divmod(expansion,slot);q,c=divmod(head,R)
            assert c==(comb(M,V) if V<=M else 0)
            assert (c%2==1)==contained(M,V)
            nsub+=1
            if c%2:
                hh=(c-1)//2;dg=R-c;rg=slot-rem
                assert min(q,hh,rem)>=0 and min(dg,rg)>0
                assert expansion==(q*R+2*hh+1)*slot+rem
                assert 2*hh+1+dg==R and rem+rg==slot
                nconstruct+=1
    nand=0
    for X,Y,Z in product(range(40),repeat=3):
        a=X-Z;c=Y-Z
        accept=min(a,c)>=0 and contained(X,Z) and contained(Y,Z) and contained(a+c,a)
        assert accept==(Z==X&Y)
        nand+=1
    nspread=0
    for b in (2,4,8,32):
        for n in range(1,5):
            codes=range(b**n) if b**n<=4096 else [0,1,b-1,b**(n-1),b**n-1,(b**n-1)//(b-1)]
            for stride in (n+1,n+2,2*n+3):
                for u in codes:spread(u,b,n,stride);nspread+=1
    nconvert=0
    for n in range(1,8):
        for L in (n+1,n+3):
            for variant in range(17):
                ds=[(11*i+variant)%16 for i in range(n)]
                u=sum(v*32**i for i,v in enumerate(ds))
                got=spread(u,32,n,L)
                assert got==sum(v*(32**L)**i for i,v in enumerate(ds))
                nconvert+=1
    # Raw tile bitplanes: enumerate all valid candidate plane triples at two slots.
    J=1+32;nplanes=0
    masks=[0,1,32,33]
    accepted=set()
    for a,b,c in product(masks,repeat=3):
        valid=contained(J,b+c);T=a+2*b+4*c
        if valid:accepted.add(T)
        nplanes+=1
    assert accepted=={a+32*b for a,b in product(range(6),repeat=2)}
    for code in range(32**3):
        assert contained(15*J,code)==(code<32**2 and code%32<16 and code//32<16)
    npairs=0
    for variant in range(300):
        fields=[(variant*(i+1)+i*i)%19 for i in range(11)]
        z=fields[-1]
        for x in fields[-2::-1]:z=pair(x,z)
        got=[]
        for _ in range(10):x,z=unpair(z);got.append(x)
        got.append(z);assert got==fields;npairs+=1
    # Required zero-exponent and zero-input edges are explicitly included above.
    result={'verdict':'PASS','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'inherited_pell_source_sha256':h,'genuine_power_witnesses':powers,
        'exact_binomial_extraction_cases':nsub,'positive_sub_witness_constructions':nconstruct,
        'candidate_AND_triples':nand,'SPREAD_cases':nspread,'fixed_32_conversion_cases':nconvert,
        'tile_plane_candidates':nplanes,'patch_range_cases':32**3,'cantor_11_field_roundtrips':npairs,
        'submitted_programs_executed_or_imported':False,
        'proof_status':'Finite corroboration only; universal POWER depends on pinned constructive Pell theorem.'}
    (HERE/'arithmetic-audit-receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
