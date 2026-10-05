#!/usr/bin/env python3
"""Fresh evidence for the resonant PLUS population theorem; predecessors inert."""
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path

BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers')
PINS = {
 '1980/FIXED_RAW_UNIVERSAL_78_PROOF.md':'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39',
 '1980/FIXED_RAW_UNIVERSAL_77_PROOF.md':'292acdfe5ff598201c3dd9cd7defff07b45d743637c1f3836a21065888053a41',
 '1980/FIXED_RAW_UNIVERSAL_76_PROOF.md':'75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
 'research-wip/native-stream-queue/complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'research-wip/native-stream-queue/complete83_shared_projection_scout.json':'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
 'research-wip/native-stream-queue/complete83_outer_family_sparse_two_primary.md':'bda0275af08ceaf1637b6bfa3ba8a8347205f5a674783cec7105ca263bf3fb97',
 'research-wip/native-stream-queue/complete83_outer_family_uniform_two_primary.md':'3ad273d152dbb7a6acc2d312c9963e373adc0e194f6f9c8e685b2cebcb548e12',
 'research-wip/native-stream-queue/complete83_source_coupled_input_lifting.md':'822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f',
 'research-wip/native-stream-queue/complete83_fixed_prime_quotient_carries.md':'53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46',
 'research-wip/native-stream-queue/complete83_subpower_selector_bound.md':'3c52050218676fa59fdd83f60699e0d884b1e885e16cc3864146d6dd66010eb4',
}

def check(value, message):
    if not value:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

# Seven-variable exact polynomial arithmetic, written for these two identities.
NVAR=7
ZERO=(0,)*NVAR

def const(c):
    return {ZERO:Fraction(c)} if c else {}

def var(i):
    e=list(ZERO); e[i]=1
    return {tuple(e):Fraction(1)}

def add(*items):
    result=defaultdict(Fraction)
    for item in items:
        for e,c in item.items(): result[e]+=c
    return {e:c for e,c in result.items() if c}

def mul(a,b):
    result=defaultdict(Fraction)
    for e,c in a.items():
        for f,d in b.items(): result[tuple(x+y for x,y in zip(e,f))]+=c*d
    return {e:c for e,c in result.items() if c}

def scale(a,c):
    return mul(a,const(c))

def power(a,n):
    out=const(1)
    for _ in range(n): out=mul(out,a)
    return out

def identities():
    qbase,F,z,S,U,f,h=map(var,range(NVAR))
    q=scale(add(power(qbase,2),qbase),Fraction(1,2))
    direct=scale(add(mul(add(power(q,2),scale(mul(q,F),-1),scale(z,-1)),add(power(q,2),const(-1))),S),16)
    expanded=add(power(qbase,8),scale(power(qbase,7),4),
      mul(add(const(6),scale(F,-2)),power(qbase,6)),
      mul(add(const(4),scale(F,-6)),power(qbase,5)),
      mul(add(scale(F,-6),scale(z,-4),const(-3)),power(qbase,4)),
      mul(add(scale(F,-2),scale(z,-8),const(-8)),power(qbase,3)),
      mul(add(scale(F,8),scale(z,-4),const(-4)),power(qbase,2)),
      scale(mul(F,qbase),8),scale(z,16),scale(S,16))
    check(direct==expanded,'fresh 16R polynomial identity including +16z')
    # Reuse F as the independent lower z limb for the second formal identity.
    zlow=F
    originalF=add(mul(U,qbase),f)
    originalZ=add(mul(h,qbase),zlow)
    source=scale(add(mul(add(power(q,2),scale(mul(q,originalF),-1),scale(originalZ,-1)),add(power(q,2),const(-1))),S),16)
    tail=add(scale(S,16),
      mul(add(scale(f,-2),scale(zlow,-8),const(-8),scale(U,8),scale(h,-4)),power(qbase,3)),
      mul(add(scale(f,8),scale(zlow,-4),const(-4),scale(U,8)),power(qbase,2)),
      mul(add(scale(f,8),scale(h,16)),qbase),scale(zlow,16))
    high=add(power(qbase,8),mul(add(const(4),scale(U,-2)),power(qbase,7)),
      mul(add(const(6),scale(f,-2),scale(U,-6)),power(qbase,6)),
      mul(add(const(4),scale(f,-6),scale(U,-6),scale(h,-4)),power(qbase,5)),
      mul(add(scale(f,-6),scale(zlow,-4),const(-3),scale(U,-2),scale(h,-8)),power(qbase,4)))
    check(source==add(high,tail),'two-limb formal identity')
    return {'identities':2,'expanded_terms':len(expanded),'limb_terms':len(source),'exact_rational_coefficients':True}

SOURCE_ROWS=[
 ['repunit','*','Bm1','Jrep'],['q','+','repunit',1],['Lbig','*','q','q'],
 ['q_minus_F','-','q','F'],['q_minus_FZ','-','q_minus_F','Z'],
 ['gap_product','*','repunit','q_minus_F'],['gap','+','gap_product','q_minus_FZ'],
 ['Lm1','-','Lbig',1],['rproduct','*','gap','Lm1'],['qMF','*','q','MF'],
 ['mask_factor','+','MC','qMF'],['mask','*','mask_factor','Jrep'],['r_lhs','+','rproduct','mask']]

def cyclic_checks():
    count=0
    for d in range(2,10):
        B=1<<d; m=B-1
        for value in range(0,20*B+7):
            folded=value
            while folded>m:
                quotient,remainder=divmod(folded,B)
                next_value=quotient+remainder
                check(next_value.bit_count()<=folded.bit_count(),'single cyclic fold')
                folded=next_value
            residue=0 if folded==m else folded
            check(residue==value%m and residue.bit_count()<=value.bit_count(),'cyclic reduction')
            count+=1
    return count

def census_checks():
    rows=[]
    for a in range(1,5):
      for k in range(2,10):
       for extra in (0,2,5):
        w=max(2,(k+1).bit_length())
        t=extra
        while 2*w+30*a+9+2*t < k+9*a+5: t+=1
        mask=(1<<w)-2
        for j in range(1,9*a+5+t): mask += 1<<(w*j)
        # Each selector meets one occupancy, nine copy, and four anchor clauses.
        selector_coeffs=[]
        for selector in range(k):
            bits={0}
            for slot in range(9): bits.add(w*(1+slot*a+(selector+2*slot)%a))
            for anchor in range(4): bits.add(w*(1+9*a+anchor))
            selector_coeffs.append(sum(1<<b for b in bits))
        coefficient_population=sum(c.bit_count() for c in selector_coeffs)+9*a+4
        native=2*mask.bit_count()+12*a+3
        dummy=native-k-9*a-4
        E0=k+12*a+dummy-1; M=E0+3*a+1
        check(mask.bit_count()==w+9*a+3+t,'clause mask census')
        check(coefficient_population==14*k+9*a+4,'literal clause occurrence census')
        check(dummy>=1 and M==native+6*a-4 and M>=k+15*a and M>=45,'layout census')
        population_bound=2*coefficient_population+6
        check(population_bound==28*k+18*a+14<28*M,'sharpened K bound')
        # Choose a relaxed but valid larger fixed radix; no compiler execution.
        b=1
        mass=4*(native+2)*(2*(sum(selector_coeffs)+sum(1<<(w*j) for j in range(1,9*a+5)))+6)+8
        while (1<<b)<max(mass,2*mask+4,16): b*=5
        L=1
        while L<=213*M+4*a+4: L*=5
        d=b*L
        check(M<3*b and d>71*M*M and native<=M-2,'layout/radix margin')
        check(2*d-2*native-5*population_bound*native>0,'positive uniform margin')
        rows.append({'a':a,'k':k,'zero_clauses':t,'w':w,'N':native,'M':M,'b':b,'L':L,'d':d,'K_population_upper':population_bound})
    return rows

def example(d,n,K,missing,h):
    B=1<<d; m=B-1; Q=1<<(d*n); D=d*n
    MC=m-missing; MF=2*B-3
    H=(m+missing)//2; P=(Q-1)//m
    check(MC>0 and MC%4==2 and missing%4==1 and K%2==0,'synthetic fixed signs')
    C,V=divmod(K*H,m)
    U=C+K*h; a=K-C+K*h; c=h+1
    f=V*P+a; low=H*P+c
    z=low+h*Q; F=f+U*Q
    check(F==K*z and z==1+H*P+(Q+1)*h,'resonant producers')
    q=Q*(Q+1)//2; J=(q-1)//m; S=(MC+q*MF)*J
    R=(q*q-z-q*F)*(q*q-1)+S
    check(R>0 and (R+1)%(Q+1)==0,'positive resonant index')
    check(0<S<2*q*q and 0<f<Q and 0<low<Q and Q>=64 and 64*max(U,h)<=Q,'tail domain')
    tail=16*S+(-2*f-8*low-8+8*U-4*h)*Q**3+(8*f-4*low-4+8*U)*Q**2+(8*f+16*h)*Q+16*low
    epsilon=tail//Q**4
    check(-11<=epsilon<=8,'bounded tail carry')
    s4,v4=divmod(6*V+4*H,m);s5,v5=divmod(6*V,m);s6,v6=divmod(2*V,m)
    beta4=6*a+2*U+12*h+7-epsilon-s4
    beta5=6*a+6*U+4*h+s4-3-s5
    beta6=2*a+6*U+s5-5-s6
    delta7=2*U+s6-3
    betas=[beta4,beta5,beta6]
    residues=[v4,v5,v6]
    deficits=[v*P+b for v,b in zip(residues,betas)]+[delta7]
    check(all(0<v<Q for v in deficits) and all(b>0 for b in betas),'four deficits')
    number=16*R
    digits=[(number//Q**j)%Q for j in range(4,8)]
    check(digits==[Q-v for v in deficits] and number//Q**8==0,'four exact high digits and terminal borrow')
    high_error=sum((b-1).bit_count() for b in betas)+(delta7-1).bit_count()
    residue_pop=sum(v.bit_count() for v in residues)
    check(residue_pop<=5*V.bit_count()+H.bit_count(),'residue population estimate')
    check(sum(v.bit_count() for v in digits)>=4*D-n*residue_pop-high_error,'high population')
    W=(MC//2)*P
    check(W+h<Q//2 and R%Q==W+h+Q//2,'low exact word without wrapping')
    t=(h.bit_length()+d-1)//d
    check(t+1<n,'low block domain')
    low_digits=[((R%Q)//B**j)%B for j in range(n)]
    for j in range(t+1,n):
        check(low_digits[j]==MC//2+(B//2 if j==n-1 else 0),'unchanged dense low block')
    low_bound=(n-t-1)*MC.bit_count()+1
    check((R%Q).bit_count()>=low_bound,'low population')
    N=missing.bit_count()
    check(H.bit_count()==N and MC.bit_count()==d-N,'mask complement population')
    mu=2*d-2*N-5*V.bit_count()
    combined=3*D+n*mu-high_error-(t+1)*MC.bit_count()+1
    check(R.bit_count()>=combined,'complete finite lower bound')
    return {'d':d,'n':n,'K':K,'missing_mask':missing,'h':h,'U':U,'V':V,'epsilon':epsilon,'beta':betas,'delta7':delta7,'R_bits':R.bit_length(),'R_population':R.bit_count(),'finite_lower_bound':combined,'target':3*D-1,'mu':mu,'binary_target_pass':R.bit_count()>=3*D-1,'original_z_class':z%4==1,'R_sha256':sha(hex(R).encode())}

def build():
    dependencies=[]
    for path,pin in PINS.items():
        data=(BASE/path).read_bytes();check(sha(data)==pin,'pin '+path)
        dependencies.append({'path':path,'bytes':len(data),'sha256':pin})
    packet=json.loads((BASE/'research-wip/native-stream-queue/complete83_shared_projection_scout.json').read_text())['packet']
    table={row[0]:row for row in packet['source']}
    for row in SOURCE_ROWS: check(table[row[0]]==row,'literal source '+row[0])
    fixtures=[]
    for d in (8,16,25):
      m=(1<<d)-1
      for K in (2,32,2*m,2*(1<<d)+8):
       for n in (9,13,25):
        for h in (1,n,n*n,1<<((d*n).bit_length()+2)):
         fixtures.append(example(d,n,K,1+(1<<2)+(1<<(d-2)),h))
    return {'schema':'complete83 plus resonant population fresh evidence v1','helper_sha256':sha(Path(__file__).read_bytes()),'dependencies':dependencies,'source_rows':SOURCE_ROWS,'formal':identities(),'cyclic_cases':cyclic_checks(),'census_cases':census_checks(),'synthetic_resonant_cases':fixtures,'scope':{'new_helper_only':True,'predecessor_executed':False,'actual_compiler_instantiated':False,'full_source_evaluated':False,'Pell_or_half_binomial_materialized':False,'synthetic_cases_are_full_source_zeros':False,'shifted_selector_search_proved_here':False,'universal83_claim':False},'status':'PASS'}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);parser.add_argument('--expect',type=Path);args=parser.parse_args()
    check(bool(args.output)^bool(args.expect),'supply exactly one output or expect')
    value=build();data=(json.dumps(value,sort_keys=True,indent=2)+'\n').encode()
    if args.output:
        with args.output.open('xb') as stream:stream.write(data)
    else: check(args.expect.read_bytes()==data,'exact receipt replay')
    print(json.dumps({'status':'PASS','source_rows':len(value['source_rows']),'formal_identities':value['formal']['identities'],'cyclic_cases':value['cyclic_cases'],'census_cases':len(value['census_cases']),'synthetic_resonant_cases':len(value['synthetic_resonant_cases'])},sort_keys=True))
