"""Independent three-state audit of known independent-gamma87 order filters.

The additional seven-local fixture satisfies the genuine main-kernel range, but no
complete compiler history or false-input zero is supplied. Parent source frozen.
The earlier compiler_order_filters packet proves the digit method and stronger caps.
"""
import argparse
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from math import comb,gcd,isqrt
import json
from pathlib import Path

import complete75_independent_gamma87_period as prior
import complete75_gamma87_compiler_order_filters as earlier_filters
candidate=prior.parent


def prime(p):
    return type(p)is int and p>=2 and all(p%d for d in range(2,isqrt(p)+1))


@lru_cache(None)
def binomial_table(p):
    assert prime(p) and p%2
    rows=[]
    for n in range(p):
        row=[1]*(n+1)
        for k in range(1,n):row[k]=(rows[n-1][k-1]+rows[n-1][k])%p
        rows.append(tuple(row))
    return tuple(rows)


def upper_tail(r,X,p):
    """sum_(k=r)^(2r) binom(2r,k) X^k mod odd prime p, by three-state digit DP."""
    assert type(r)is int and r>=0
    table=binomial_table(p);X%=p;n=2*r;rr=r;digits=[]
    while n or rr:
        digits.append((n%p,rr%p));n//=p;rr//=p
    weights=[1]
    for k in range(1,p):weights.append(weights[-1]*X%p)
    states={0:1}
    for ni,ri in reversed(digits):
        nxt={}
        for relation,value in states.items():
            for ki in range(ni+1):
                following=relation if relation else (ki>ri)-(ki<ri)
                nxt[following]=(nxt.get(following,0)+value*table[ni][ki]*weights[ki])%p
        states=nxt
    return (states.get(0,0)+states.get(1,0))%p


def genuine_a_mod_prime(R,p):
    assert type(R)is int and R>=3 and R%2
    assert prime(p) and p%2
    r=(R-1)//2;X=pow(2,R,p)
    M=upper_tail(r,X,p)*pow(pow(X,r,p),-1,p)%p
    return M*pow(2,-1,p)*(X+1)%p


def lucas(n,k,p):
    table=binomial_table(p);value=1
    while n or k:
        ni,ki=n%p,k%p
        if ki>ni:return 0
        value=value*table[ni][ki]%p;n//=p;k//=p
    return value


def digit_audit():
    tally=Counter()
    for R in range(3,515,4):
        r=(R-1)//2;cs=[comb(2*r,r+j) for j in range(r+1)]
        for p in (3,5,7,11,13,31,127):
            X=pow(2,R,p)
            direct=sum(c*pow(X,j,p) for j,c in enumerate(cs))*pow(2,-1,p)*(X+1)%p
            assert direct==genuine_a_mod_prime(R,p)
            tally['direct_exact_binomial_residue_checks']+=1
    # Exact independent full-binomial reciprocity, at large integer indices.
    for R in ((1<<64)-1,(1<<127)+3,(1<<511)-1,(1<<1024)+7):
        r=(R-1)//2
        for p in (3,5,7,31,127):
            X=pow(2,R,p);left=upper_tail(r,X,p)+pow(X,2*r,p)*upper_tail(r,pow(X,-1,p),p)
            right=pow(X+1,2*r,p)+lucas(2*r,r,p)*pow(X,r,p)
            assert (left-right)%p==0
            tally['large_index_tail_reciprocity_checks']+=1
    return dict(tally)


def factor_small(n):
    result={};p=2
    while p*p<=n:
        while n%p==0:result[p]=result.get(p,0)+1;n//=p
        p+=1
    if n>1:result[n]=result.get(n,0)+1
    return result


def exact_order(H):
    assert H>1 and H%2
    v=2%H;order=1
    while v!=1:v=2*v%H;order+=1
    return order


def prime_power_audit():
    counts=Counter();examples=[]
    for a in range(6,3601,6):
        H=4*a+3;Delta=(a+1)*(a+3);O=exact_order(H)
        assert gcd(H,Delta) in (3,9)
        primes_H=factor_small(H)
        for p,exponent in factor_small(Delta).items():
            if p<5:continue
            side=1 if (a+1)%p==0 else 3
            for k in range(1,exponent+1):
                w=p**k
                assert (a+side)%w==0 and H%w==(-1 if side==1 else -9)%w
                bound=(w+1)*(w-1 if side==1 else w-9)
                cap=isqrt(H+1) if side==1 else 4+isqrt(H+25)
                if O%w==0:
                    witnesses=[ell for ell in primes_H if (ell-1)%w==0]
                    assert witnesses and H>=bound and w<=cap
                    for ell in witnesses:
                        assert H//ell>=w-(1 if side==1 else 9)
                    counts['positive_order_components_with_explicit_prime_witness']+=1
                if H<bound:
                    assert O%w!=0
                    counts['factorization_free_excluded_components']+=1
                    if len(examples)<8:examples.append(dict(a=a,H=H,p=p,k=k,side=side,lower_bound=bound))
                counts['Delta_prime_power_components_checked']+=1
        counts['small_exact_order_hosts']+=1
    return dict(checks=dict(counts),examples=examples,
        scope='Small arithmetic hosts check the uniform implication. They are not complete main kernels or compiler histories.')


def local_seven_fixture():
    R,q,d=753407,32,5;r=(R-1)//2
    assert R%4==3 and q>=16 and 3*q+1<=R<q**4 and R.bit_count()==17
    assert R.bit_count()>=3*(q.bit_length()-1)+2
    residues={p:genuine_a_mod_prime(R,p) for p in (7,127)}
    assert residues=={7:6,127:31}
    assert all(earlier_filters.native_a_residue(R,p)[0]==v for p,v in residues.items())
    assert prime(127) and pow(2,7,127)==1 and pow(2,1,127)!=1 and prime(7)
    # Independently sum every upper-half Lucas coefficient, no prefix DP.
    terms=0
    for p in (7,127):
        X=pow(2,R,p);power=1;total=0
        for j in range(r+1):
            total=(total+lucas(2*r,r+j,p)*power)%p;power=power*X%p;terms+=1
        assert total*pow(2,-1,p)*(X+1)%p==residues[p]
    assert gcd(7,2*d)==1
    return dict(R=R,q=q,scalar_width=d,popcount_R=R.bit_count(),r0=r,a_residues=residues,
        prime_modulus=127,exact_order_of_two=7,forced_alias_divisor=7,
        prior_two_state_evaluator_agrees=True,
        explicit_upper_half_Lucas_terms=terms,
        full_half_binomial_kernel_recipe='X=2^R; Y=(sum_(j=0)^r0 binom(2r0,r0+j)X^j)/2; '
            'D0=q^3. The reviewed half-binomial theorem gives the positive main/first/strong extension.',
        actual_width_consequence='For any actual compiler history meeting these residue tests, '
            'd is a power of5, so every history-preserving ordinary-input alias satisfies x=x0 mod7.',
        scope='The fixed R,q meet the full main-kernel range and population prerequisites. '
            'No masks, transport, actual compiled history or full candidate zero are supplied; giant X,Y,H are not materialized.')


def unchanged_source():
    _,certificate,pairs,polynomial=candidate.sources()
    assert len(certificate)==86 and len(polynomial)==87 and pairs==[('eight_units',1)]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in polynomial)
    assert counts=={'M':47,'A':40}
    consumers=lambda v:[n for n,_,a,b in certificate if v in(a,b)]
    assert consumers('rho')==['modulus_multiple'] and consumers('sigma')==['gam']
    assert consumers('x')==['scaled_t'] and consumers('alpha')==['C_after_alpha']
    return dict(source_sha256=sha256(json.dumps(polynomial).encode()).hexdigest(),
        polynomial_operations=87,multiplications=47,additions_subtractions=40,
        positive_witnesses=len(candidate.RETAINED),exact_degree=151,
        source_changed=False,candidate_status='unresolved',
        established_independent_bounds='75-operation comparison certificate; normalized87 polynomial of degree203.')


def verify():
    return dict(status='PASS_INDEPENDENT_GAMMA87_LOCAL_FILTERS',source=unchanged_source(),
        digit_DP=digit_audit(),prime_power_order_obstruction=prime_power_audit(),
        seven_local_fixture=local_seven_fixture(),
        audited_coarse_implication='For p>=5 and p^k|Delta, a shared order component forces '
            'H>=(p^k+1)(p^k-1) if p^k|a+1, or H>=(p^k+1)(p^k-9) if p^k|a+3. '
            'These caps are weaker than the earlier parity/mod3 bounds. The three-state '
            'Lucas implementation independently evaluates the same known half-binomial residue.',
        prior_result=dict(packet='complete75_gamma87_compiler_order_filters',
            scope='Already proves the two-state digit method, strictly stronger prime-power caps, '
                'actual compiler residue restrictions, and proper-factor certificates. '
                'The present packet adds an independent implementation/audit and a seven-local kernel fixture.'),
        reason_Dirichlet_transfer_fails='The retained positive width and complete main kernel force '
            'X=2^R and the unique half-binomial Y; H cannot be varied independently after fixing R.',
        scope='Independent audit of previously proved local filters, with an additional seven-local kernel fixture; '
            'no actual compiled false-input witness, universality proof or new universal operation bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['digit_DP']);print(result['prime_power_order_obstruction']['checks'])
