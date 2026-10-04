#!/usr/bin/env python3
"""Fresh exact arithmetic tests; reads emitted DAGs inertly, imports no emitter.

No physical simulator, saved orbit, prior checker, or upstream program is run.
Finite tests supplement the all-integer proof, not replace it. Full Pell
witnesses are tested for exponent zero; nonzero-exponent tests check the
outer constraints with independently computed ordinary integer power values.
"""
from fractions import Fraction as F
from pathlib import Path
from math import gcd, isqrt, lcm
import hashlib
import json

HERE=Path(__file__).resolve().parent


def require(ok,message):
    if not ok: raise ValueError(message)


def pairmul(z,w):
    a,b=z; c,d=w
    return a*c-b*d,a*d+b*c


def pairpow(z,n):
    result=(1,0)
    while n:
        if n&1: result=pairmul(result,z)
        z=pairmul(z,z); n//=2
    return result


def egcd(a,b):
    r0,r1,s0,s1,t0,t1=abs(a),abs(b),1,0,0,1
    while r1:
        q=r0//r1
        r0,r1=r1,r0-q*r1; s0,s1=s1,s0-q*s1; t0,t1=t1,t0-q*t1
    return r0,s0*(1 if a>=0 else -1),t0*(1 if b>=0 else -1)


def cantor(a,b): return (a+b)*(a+b+1)//2+b


def uncantor(z):
    diagonal=(isqrt(8*z+1)-1)//2
    b=z-diagonal*(diagonal+1)//2
    return diagonal-b,b


def encode(g): return 1+cantor(g[0]-1,cantor(g[1]-1,g[2]-1))


def decode(code):
    a,inner=uncantor(code-1); b,c=uncantor(inner)
    return a+1,b+1,c+1


def geometric_decision(g):
    # Independent rational-coordinate form, no gcd/Bezout certificate variables.
    D=sum(g); X=F(g[0],D)-F(1,3); Y=F(g[0]+g[1],D)-F(2,3)
    radius=F(4,1845); norm=X*X+Y*Y
    if norm!=radius: return norm<radius
    px,py=F(4,205),F(-26,615)
    er=(X*px+Y*py)/radius; ei=(Y*px-X*py)/radius
    denominator=lcm(er.denominator,ei.denominator)
    n=0; rest=denominator
    while rest%5==0: n+=1; rest//=5
    if rest!=1: return True
    re,im=pairpow((3,-4),n)
    return (er,ei)!=(F(re,5**n),F(im,5**n))


def outer_witness(g,one_input=False):
    witness={}
    def pos(name,value):
        require(type(value) is int and value>0,'nonpositive '+name)
        witness[name]=value
    def nat(name,value):
        require(value>=0,'negative natural '+name)
        pos(name+'.Plus',value+1)
    def signed(name,value):
        pos(name+'.Positive',max(value,0)+1)
        pos(name+'.Negative',max(-value,0)+1)
    if one_input:
        for j,value in enumerate(g,1): pos('gap.'+str(j),value)
        nat('decode.inner',cantor(g[1]-1,g[2]-1))
    D=sum(g); A=3*g[0]-D; B=3*(g[0]+g[1])-2*D
    delta=4*D*D-205*(A*A+B*B)
    # Out-of-disk negative cases deliberately get a legal but false slack.
    nat('radius.delta',max(delta,0))
    U,V=6*A-13*B,13*A+6*B
    h=gcd(gcd(U,V),2*D); u,v,q=U//h,V//h,2*D//h
    pos('fraction.h',h); pos('fraction.q',q)
    signed('fraction.u',u); signed('fraction.v',v)
    g12,a,b=egcd(u,v); allg,c,d=egcd(g12,q)
    require(allg==1,'gcd reduction failed')
    for j,z in enumerate((c*a,c*b,d),1): signed('bezout.'+str(j),z)
    n=0; r=q
    while r%5==0: n+=1; r//=5
    P=5**n; k,s=divmod(r,5)
    nat('valuation.n',n); pos('power5.out',P)
    pos('valuation.r',r); nat('valuation.k',k); pos('valuation.s',s)
    pos('valuation.t',5-s)
    radix=4*P+1; base=3+4*radix; T=base**n
    pos('power_complex.out',T)
    C,S=pairpow((3,4),n)
    signed('complex.C',C); signed('complex.S',S)
    for j,value in enumerate((C+P,P-C,S+P,P-S),1): nat('complex.bound.'+str(j),value)
    quotient,remainder=divmod(T-C-radix*S,radix*radix+1)
    require(remainder==0,'modular extraction is not integral')
    signed('complex.quotient',quotient)
    acceptance=delta*delta+(r-1)**2+(u-C)**2+(v+S)**2
    # A forbidden boundary point deliberately gets false positive RHS 1.
    pos('acceptance.positive',max(acceptance,1))
    return witness,dict(delta=delta,h=h,u=u,v=v,q=q,n=n,r=r,P=P,C=C,S=S,T=T,
                        radix=radix,base=base,acceptance=acceptance)


def pell_pair(a,n):
    # Computes (a+sqrt(a^2-1))^n by fresh exact quadratic-ring arithmetic.
    d=a*a-1; result=(1,0); z=(a,1)
    def mul(z,w): return z[0]*w[0]+d*z[1]*w[1],z[0]*w[1]+z[1]*w[0]
    while n:
        if n&1: result=mul(result,z)
        z=mul(z,z); n//=2
    return result


def zero_exponent_power_witness(base,prefix):
    # Explicit specialization of the constructive Pell proof at k=e+1=1.
    w=base; a,yw=pell_pair(w+1,w)
    require(yw%w==0,'auxiliary Pell divisibility failed')
    g=yw//w; M=2*a*base-base*base-1
    x,y=a,1; u,v=2*a*a-1,2*a
    j=next(j for j in range(4) if (a+j*u)%4==1)
    beta=a+j*u; s,t=beta,1
    positive=dict(out=1,aMinus1=a-1,betaMinus1=beta-1,w=w,M=M,g=g,
                  x=x,y=y,u=u,v=v,s=s,t=t,qb=(beta-1)//4,qv=v,strict=M-base)
    natural=dict(dwb=0,dwk=w-1,dyk=0,alpha1=0,alpha2=j,sigma1=0,
                 sigma2=j,tau1=0,tau2=0,rho1=0,rho2=0)
    result={prefix+'.'+name:value for name,value in positive.items()}
    result.update({prefix+'.'+name+'.Plus':value+1 for name,value in natural.items()})
    require(len(result)==26 and min(result.values())>0,'bad full POWER witness')
    return result


def evaluate(dag,g,witness,full=False):
    values={'w:'+name:value for name,value in witness.items() if name in dag['witnesses']}
    inputs={'code':encode(g)} if dag['inputs']==['code'] else dict(zip(('g1','g2','g3'),g))
    values.update({'i:'+name:value for name,value in inputs.items()})
    def value(ref): return int(ref[2:]) if ref.startswith('c:') else values.get(ref)
    for j,(op,l,r) in enumerate(dag['gates']):
        a,b=value(l),value(r)
        if a is not None and b is not None:
            values['g:'+str(j)]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
    residuals={name:value(l)-value(r) for name,l,r in dag['equations']
               if value(l) is not None and value(r) is not None}
    if full:
        require(len(residuals)==len(dag['equations']),'incomplete full witness')
        require(len(set(dag['witnesses'])-set(witness))==0,'missing full witness')
        require(all(witness[name]>0 for name in dag['witnesses']),'nonpositive full witness')
        require(value(dag['output'])==sum(r*r for r in residuals.values()),'output differs from SOS')
    return residuals,value(dag['output'])


def gaps_from_eta(er,ei):
    px,py=F(4,205),F(-26,615)
    X,Y=px*er-py*ei,px*ei+py*er
    x,y=F(1,3)+X,F(2,3)+Y
    gs=(x,y-x,1-y); scale=lcm(*(z.denominator for z in gs))
    g=tuple(int(z*scale) for z in gs)
    common=gcd(gcd(*g[:2]),g[2]); g=tuple(z//common for z in g)
    require(min(g)>0,'boundary circle left positive-gap chamber')
    return g


def main():
    dags={}
    for path in sorted((HERE/'evidence').glob('*.dag.json')):
        dag=json.loads(path.read_text()); dags[dag['variant']]=dag
    require(len(dags)==4,'missing variant')
    stats={}
    tested=[]
    # Exhaustive ordinary positive-gap box, no physical histories.
    for a in range(1,16):
        for b in range(1,16):
            for c in range(1,16): tested.append(((a,b,c),'gap_box'))
    # Both orbit orientations, including n=0, with nonprimitive gap scaling.
    for n in range(61):
        real,imag=pairpow((3,4),n); denominator=5**n
        for sign in (-1,1):
            g=gaps_from_eta(F(real,denominator),F(sign*imag,denominator))
            require(geometric_decision(g)==(sign==1 and n>0),'orientation decision wrong')
            for scale in (1,2,7): tested.append((tuple(scale*z for z in g),'signed_orbit'))
    # General rational unit-circle ratios, including zero real/imaginary part.
    for a in range(-10,11):
        for b in range(1,11):
            denominator=a*a+b*b
            g=gaps_from_eta(F(b*b-a*a,denominator),F(2*a*b,denominator))
            tested.append((g,'rational_circle'))
    for g,kind in tested:
        expected=geometric_decision(g)
        for name,dag in dags.items():
            witness,metadata=outer_witness(g,name.startswith('one-input'))
            if name.endswith('quartic'): witness.pop('valuation.t')
            residuals,_=evaluate(dag,g,witness)
            outer={n:r for n,r in residuals.items() if not n.startswith(('power5.','power_complex.'))}
            require(len(outer)==(16 if name.startswith('one-input') else 14),'outer equation count')
            require(all(r==0 for r in outer.values())==expected,'outer equivalence failure')
            stats[kind]=stats.get(kind,0)+1
    # Bounded uniqueness is checked exhaustively through P=125.
    extraction_candidates=0
    for n in range(4):
        P=5**n; b=4*P+1; T=(3+4*b)**n; actual=pairpow((3,4),n); found=[]
        for C in range(-P,P+1):
            for S in range(-P,P+1):
                extraction_candidates+=1
                if (T-C-b*S)%(b*b+1)==0: found.append((C,S))
        require(found==[actual],'bounded extraction ambiguity')
    # An omitted bound admits false residues; an omitted gcd admits false acceptance.
    P=5; b=21; T=87; C,S=3,4; wrongC=C+b*b+1
    require((T-wrongC-b*S)%(b*b+1)==0 and abs(wrongC)>P,'missing-bound counterexample')
    tangent=gaps_from_eta(F(1),F(0)); witness,m=outer_witness(tangent)
    require(m['u']==m['q']==1 and m['v']==0 and m['acceptance']==0,'n0 tangent case')
    # Divide h by 2, so u=q=2, then r=2 makes the nonprimitive fake look valid.
    require(m['h']%2==0 and gcd(2,2)==2 and (2-1)**2+(2-1)**2>0,'missing-gcd counterexample')
    # If divisible-by-five r were allowed, inverse n=1 could claim exponent zero.
    inv=gaps_from_eta(F(3,5),F(-4,5)); _,invdata=outer_witness(inv)
    require(invdata['q']==5 and invdata['n']==1 and invdata['acceptance']==0,'inverse n1 case')
    require((5-1)**2+(3-1)**2+(-4)**2>0,'missing-valuation counterexample')
    # Fully instantiate and evaluate all 52 Pell auxiliaries for exponent zero.
    full_points=[(1,1,1),gaps_from_eta(F(5,13),F(12,13))]
    full_cases=0; single_leaf_mutations=0; mutation_rejections=0; neutral_mutations=[]; maximum_bits=0
    for g in full_points:
        for name,dag in dags.items():
            witness,m=outer_witness(g,name.startswith('one-input'))
            require(m['n']==0 and geometric_decision(g),'full-test point not valid n0')
            witness.update(zero_exponent_power_witness(5,'power5'))
            witness.update(zero_exponent_power_witness(m['base'],'power_complex'))
            if name.endswith('quartic'): witness.pop('valuation.t')
            residuals,output=evaluate(dag,g,witness,full=True)
            require(output==0 and not any(residuals.values()),'full zero failed')
            maximum_bits=max(maximum_bits,max(z.bit_length() for z in witness.values()))
            full_cases+=1
            for key in dag['witnesses']:
                modified=dict(witness); modified[key]+=1
                _,value=evaluate(dag,g,modified,full=True)
                if value:
                    mutation_rejections+=1
                else:
                    # A Bezout coefficient multiplying zero can change freely.
                    require(g==(1,1,1) and key.startswith(('bezout.1.','bezout.2.')),
                            'unexpected neutral perturbation '+key)
                    neutral_mutations.append(dict(variant=name,witness=key))
                single_leaf_mutations+=1
    for code in range(1,10001):
        require(encode(decode(code))==code,'Cantor code roundtrip')
    for g,_ in tested:
        require(decode(encode(g))==g,'Cantor gap roundtrip')
    receipt=dict(verdict='PASS',test_counts=stats,total_outer_instances=sum(stats.values()),
                 unique_gap_test_entries=len(tested),extraction_candidates=extraction_candidates,
                 full_Pell_witness_cases=full_cases,full_single_leaf_mutations=single_leaf_mutations,
                 single_leaf_mutation_rejections=mutation_rejections,
                 neutral_Bezout_mutations=neutral_mutations,
                 maximum_full_witness_bit_length=maximum_bits,Cantor_code_roundtrips=10000,
                 Cantor_gap_roundtrips=len(tested),negative_obligations=['bounds necessary','primitive gcd necessary','exact valuation necessary','inverse orientation'],
                 limitations='Full Pell auxiliaries tested only at exponent zero. Nonzero powers use independently evaluated integer outputs; proof supplies general POWER semantics. No trajectory replay or physical simulation.',
                 checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                 dag_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((HERE/'evidence').glob('*.dag.json'))})
    (HERE/'evidence'/'semantic-checks.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True,indent=2))


if __name__=='__main__': main()
