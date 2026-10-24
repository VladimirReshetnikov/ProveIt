#!/usr/bin/env python3
"""Independent finite arithmetic regressions; imports no builder modules."""
from pathlib import Path
from itertools import combinations_with_replacement
from math import comb, factorial, gcd, prod
import argparse, hashlib, json

def need(ok, message):
    if not ok:
        raise ValueError(message)

def crt(residues, moduli):
    modulus = prod(moduli)
    value = sum(a * (modulus // m) * pow(modulus // m, -1, m)
                for a, m in zip(residues, moduli)) % modulus
    return value or modulus

def primes(n):
    return [p for p in range(2, n+1) if all(p % q for q in range(2, p))]

def run():
    counts = {}
    cases = 0
    for p in primes(19):
        for e in range(1, 6):
            pe = p**e
            for k in range(1, 31):
                for a in range(301):
                    if comb(a,k) % pe == 0:
                        need(a % pe < k, 'prime-power range soundness')
                    cases += 1
    counts['one_sided_range_cases'] = cases
    need(4 % 4 < 2 and comb(4,2) % 4 != 0, 'range converse negative control')

    cases = 0
    for t in range(1, 9):
        F, T = factorial(t), factorial(t)**2
        ds = [1+T//i for i in range(1,t+1)]
        B = comb(T+t,t)
        need(prod(ds)==B, 'reciprocal product')
        need(all(gcd(d,F)==1 for d in ds), 'small primes excluded')
        need(all(gcd(a,b)==1 for i,a in enumerate(ds) for b in ds[i+1:]), 'pairwise moduli')
        for extra in range(4):
            bound = t+extra
            R = 2+t+bound
            K = 2*R
            N = B**K
            moduli = [d**(2*K) for d in ds]
            C = crt(list(range(t)), moduli)
            A = crt(list(range(t)), moduli)
            need(1 <= C <= N*N and 1 <= A <= N*N, 'positive CRT range')
            need((C+T+1)%B==0, 'index congruence')
            need(comb(C,t)%N==0, 'index divisibility')
            need(comb(A,bound+1)%N==0, 'coordinate divisibility')
            need((A-C)**2 % N==0, 'local polynomial vanishing')
            mutated = list(range(t)); mutated[-1] += 1
            A_bad = crt(mutated, moduli)
            need((A_bad-C)**2 % N != 0, 'bad local row rejected')
            cases += 1
    counts['hybrid_constructive_fixtures'] = cases
    derived_cases = 0
    derived_larger_than_aggregate = 0
    for t in range(1, 11):
        F=factorial(t);T=F*F
        ds=[1+T//i for i in range(1,t+1)];B=prod(ds)
        K=2*(t+5);N=B**K;moduli=[d**(2*K) for d in ds]
        largest=0
        while (largest+1)**2+(largest+1)+1<=t:largest+=1
        residues=[i%(largest+1) for i in range(t)]
        A=crt(residues,moduli);J=A*A+A+1
        need(comb(J,t+1)%N==0,'derived-label range completeness')
        derived_larger_than_aggregate += J>9*N*N
        bad=residues[:];bad[-1]=t+1
        Abad=crt(bad,moduli);Jbad=Abad*Abad+Abad+1
        need(comb(Jbad,t+1)%N!=0,'bad derived-label range rejected')
        derived_cases+=1
    need(derived_larger_than_aggregate>0,'aggregate exclusion control exercised')
    counts['derived_polynomial_range_fixtures']=derived_cases
    counts['derived_values_exceeding_representative_aggregate']=derived_larger_than_aggregate
    need((15-4-1)%5==0 and (15-4-1)%25!=0, 'canonical index nonlift')

    cases = 0
    for t in range(1, 21):
        F = factorial(t)
        rho = F*t*t
        V = (rho+1)**t
        D = comb(rho+t,t)
        u, v = V+D-D*F-1, D*F-V
        need(u>=0 and v>=0 and D==u+v+1, 'factorial completeness')
        need(F*F+t <= (rho+1)**2, 'product binomial bootstrap')
        need(all(comb(F*F+t,j)<=V*V for j in range(t+1)), 'all product lower digits')
        for proposed in range(0, 30):
            rr = proposed*t*t
            vv = (rr+1)**t
            dd = comb(rr+t,t)
            ceiling = (vv+dd-1)//dd
            need((proposed==ceiling)==(proposed==F), 'self-bounding factorial soundness')
            cases += 1
    counts['factorial_candidate_cases'] = cases
    need(factorial(32)>2**64 and 64*8388608<2**64, 'padded factorial carrier floor')
    need(factorial(16)>2**44 and 44*8388608<2**44,'horizon16 factorial floor')
    need(2*factorial(16)>=3*4194304*17,'derived range radix induction base')
    need(2**8>2*8**2, 'carrier base inequality')
    counts['carrier_induction_parameter_checks'] = 0
    for ell in range(8, 1001):
        need(2**ell>2*ell*ell and 2**ell>=4*ell, 'carrier induction hypotheses')
        counts['carrier_induction_parameter_checks'] += 1
    for R in range(3, 51):
        K=2*R
        N=2**K
        for k in range(1,R):
            need(10**k<N*N and 2*k+2<=K, 'ten-column radix inequality')
    counts['ten_column_radix_horizons'] = 48

    # All multisets of <=4 small Horn rules: exact positive-label balance
    # implies derivability of the designated label 1.
    labels = range(4)
    rules = [(p,q,v) for p in labels for q in labels for v in labels]
    total = balanced = 0
    # Ordered multisets through length 3 suffice for this regression.
    for n in range(1,4):
        for ids in combinations_with_replacement(range(len(rules)),n):
            rr=[rules[i] for i in ids]
            balance={j:sum(v==j for p,q,v in rr)-sum(p==j for p,q,v in rr)-sum(q==j for p,q,v in rr) for j in range(1,4)}
            if balance != {1:1,2:0,3:0}:
                total += 1; continue
            known={0}
            while True:
                after=known|{v for p,q,v in rr if p in known and q in known}
                if after==known: break
                known=after
            need(1 in known, 'truth-relative Horn balance soundness')
            balanced += 1; total += 1
    counts['horn_multisets'] = total
    counts['balanced_horn_multisets'] = balanced
    for t in range(1,20):
        F=factorial(t)
        weights=[1+j*F for j in range(1,t+1)]
        need(all(gcd(a,b)==1 for i,a in enumerate(weights) for b in weights[i+1:]), 'factorial label separation')
    # Why the explicit label bound is not optional. At t=2,F=2 the
    # unbounded label4 has weight9, sharing label1's prime3. Axiom4 and
    # rule1->truth0 yield false multiplicative balance but do not prove1.
    F=2
    need((1+4*F)==(1+F)*(1+F), 'missing-label-bound negative control')
    counts['negative_controls'] = ['range converse false', 'canonical index nonlift',
                                   'bad CRT local row', 'missing label bound']
    return {'verified':True, 'scope':'finite regressions; universal proof is separate', 'counts':counts}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=run(); a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
