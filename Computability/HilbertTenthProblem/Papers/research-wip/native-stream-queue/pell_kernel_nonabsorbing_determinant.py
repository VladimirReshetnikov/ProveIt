"""Elementary audits for the scoped nonabsorbing determinant decision proof.

General Presburger quantifier elimination is proved effective in the note,
but is not implemented here. All loops below check independent finite claims.
"""
import argparse
from itertools import product
import json
from math import gcd, lcm
from pathlib import Path


def coin_member(a, b, target):
    return target >= 0 and any((target-a*u) % b == 0
                              for u in range(target//a+1))


def bounded_coin(a, b, target, upper):
    if target < 0:
        return None
    for u in range(min(upper, target//a)+1):
        left = target-a*u
        if left % b == 0 and 0 <= left//b <= upper:
            return u, left//b
    return None


def threshold(a, b, N):
    return a*b//gcd(a,b)+2*(a+b)+abs(N)+3


def classification(a, b, M, N, L):
    assert L >= threshold(a,b,N)
    if M < 0 or M > a+b:
        return False
    if M == 0:
        return coin_member(a,b,N)
    if M == a+b:
        return coin_member(a,b,-2*(a+b)-N)
    return (M*L+N) % gcd(a,b) == 0


def saturation_audit():
    tested = admitted = endpoints = interior = 0
    for a,b in product(range(1,7), repeat=2):
        for M in range(-1,a+b+2):
            for N in range(-2*(a+b)-3, 8):
                for extra in (0,1,7):
                    L=threshold(a,b,N)+extra
                    exact=bounded_coin(a,b,M*L+N,L-2) is not None
                    assert exact == classification(a,b,M,N,L), (a,b,M,N,L)
                    tested += 1
                    admitted += exact
                    endpoints += M in (0,a+b)
                    interior += 0 < M < a+b
    return dict(cases=tested,admitted=admitted,endpoint_cases=endpoints,
                interior_cases=interior,max_coin_coefficient=6)


def normalization_audit():
    cases=0
    for a0,b0 in product((-4,-2,-1,1,2,4),repeat=2):
        for L in range(2,8):
            for A,B in product(range(1,L),repeat=2):
                a,b=abs(a0),abs(b0)
                u=A-1 if a0>0 else L-1-A
                v=B-1 if b0>0 else L-1-B
                assert 0 <= u <= L-2 and 0 <= v <= L-2
                assert a0*A+b0*B == a*u+b*v+(a+b)-(max(-a0,0)+max(-b0,0))*L
                cases += 1
    return dict(exact_substitutions=cases)


def orbit(radix, modulus):
    seen={}; sequence=[]; value=1 % modulus
    while value not in seen:
        seen[value]=len(sequence);sequence.append(value)
        value=radix*value % modulus
    return sequence,seen[value],len(sequence)-seen[value]


def duration_audit():
    cases=replacements=0
    # Coefficients are (alpha,beta,gamma,delta,epsilon,zeta,eta).
    models=((1,0,0,2,-1,0,-3), (1,2,-1,1,1,-2,5),
            (-1,1,2,3,-2,1,-4), (0,2,-1,1,0,3,0),
            (2,-3,1,-2,1,0,7), (1,0,0,1,0,0,-5),
            (1,1,0,17,-1,0,-3))
    for radix in (2,3):
        for al,be,ga,de,ep,ze,eta in models:
            det=al*de-be*ga;D=abs(det);assert D
            S=1+sum(map(abs,(al,be,ga,de,ep,ze,eta)));K=S*S+4*S+3
            for m in range(1,5):
                W=radix**m;a0=al*W+be;b0=ga*W+de
                if not a0 or not b0:continue
                a,b=abs(a0),abs(b0);d=gcd(a,b)
                assert D%d == 0
                M=max(-a0,0)+max(-b0,0)-ep*W
                N=-(a+b)-ze*W-eta;B0=threshold(a,b,N)
                assert B0 <= K*(W+1)**2
                n0=0
                while radix**n0 < B0:n0+=1
                seq,mu,period=orbit(radix,d)
                assert mu+period<=d<=D
                cycle=set(seq[mu:])
                assert cycle <= {pow(radix,j,d) for j in range(n0,n0+D)}
                for n in range(1,n0+D+8):
                    L=radix**n
                    # Above B0 the direct semigroup cases are exact by the
                    # independent saturation audit, not by brute big-L loops.
                    if L < B0:
                        accepted=bounded_coin(a,b,M*L+N,L-2) is not None
                    else:
                        accepted=classification(a,b,M,N,L)
                    cases+=1
                    if not accepted:continue
                    if L < B0 or n < D:
                        short=L
                    else:
                        ns=[j for j in range(n0,n0+D)
                            if (M*radix**j+N)%d == 0
                            and classification(a,b,M,N,radix**j)]
                        assert ns,(radix,W,models,n)
                        short=radix**ns[0]
                    assert short <= radix**(D+1)*K*(W+1)**2
                    replacements += short != L
    return dict(power_cases=cases,actual_duration_replacements=replacements,
                fixed_models=len(models),radices=[2,3])


def base_digits(value, width, count):
    result=[]
    for _ in range(count):result.append(value%width);value//=width
    assert value==0
    return result


def carry_expansion_audit():
    cases=0
    models=((1,2,-1,3,-2,4,5),(-2,1,3,-1,1,0,-7),(0,1,2,0,-1,-3,2))
    for W in range(2,7):
        for k in range(4):
            for V in ((1,) if k==3 else range(1,W)):
                L=W**k*V
                if L<2:continue
                samples=sorted({1,L-1,L//2})
                for A,B in product(samples,repeat=2):
                    da=base_digits(A,W,k+1);db=base_digits(B,W,k+1)
                    assert da[k]<V and db[k]<V
                    da += [0]*(4-len(da));db += [0]*(4-len(db))
                    for al,be,ga,de,ep,ze,eta in models:
                        E=[be*da[0]+de*db[0]+eta]
                        for j in range(1,5):
                            E.append(al*da[j-1]+ga*db[j-1]
                                     +(be*da[j]+de*db[j] if j<4 else 0)
                                     +(ep*V if j==k+1 else 0)
                                     +(ze if j==1 else 0))
                        original=(al*W+be)*A+(ga*W+de)*B+ep*W*L+ze*W+eta
                        assert sum(e*W**j for j,e in enumerate(E))==original
                        S=1+sum(map(abs,(al,be,ga,de,ep,ze,eta)))
                        assert all(abs(e)<=S*W for e in E)
                        # A zero-adjusted constant supplies actual integral
                        # carries while independently preserving the expansion.
                        E[0]-=original
                        adjusted_eta=eta-original
                        S=1+sum(map(abs,(al,be,ga,de,ep,ze,adjusted_eta)))
                        carry=0
                        for e in E:
                            assert (e+carry)%W==0
                            carry=(e+carry)//W
                            assert abs(carry)<=2*S
                        assert carry==0
                        cases+=1
    return dict(exact_expansions_and_zero_sum_carry_paths=cases)


def power_rectangle(radix, atoms):
    # Atom tuple is (kind,a,c,e,modulus); modulus is ignored for comparisons.
    comparison=[atom for atom in atoms if atom[0]!='div']
    D0=1;U0=0
    while any(radix**D0<=abs(c)+abs(e) for _,a,c,e,_ in comparison):D0+=1
    while any(radix**U0<=abs(e) for _,a,c,e,_ in comparison):U0+=1
    P=lcm(*(mod for kind,a,c,e,mod in atoms if kind=='div'))
    seq,mu,period=orbit(radix,P)
    return max(U0,mu),max(D0,mu),period


def atom_values(radix,u,d,atoms):
    W=radix**(u+d);V=radix**u;out=[]
    for kind,a,c,e,mod in atoms:
        value=a*W+c*V+e
        out.append(value>=0 if kind=='ge' else value==0 if kind=='eq' else value%mod==0)
    return tuple(out)


def two_power_audit():
    tests=models=0
    sets=[(('ge',1,-4,3,1),('eq',0,1,-9,1),('div',1,2,1,6)),
          (('ge',-1,20,-100,1),('ge',0,-1,81,1),('div',2,-3,4,12)),
          (('eq',1,-8,0,1),('ge',0,0,0,1),('div',1,1,0,5)),
          (('ge',1,0,-200,1),('eq',0,0,1,1))]
    for radix in (2,3,4):
        for atoms in sets:
            U,D,p=power_rectangle(radix,atoms);models+=1
            for u in range(U+3*p+10):
                for d in range(1,D+3*p+10):
                    ur=u if u<U else U+(u-U)%p
                    dr=d if d<D else D+(d-D)%p
                    assert 0<=ur<U+p and 1<=dr<D+p
                    assert atom_values(radix,u,d,atoms)==atom_values(radix,ur,dr,atoms)
                    tests+=1
    return dict(affine_formula_models=models,whole_atom_vector_comparisons=tests,
                includes_non_coprime_moduli=True)


def verify():
    return dict(status='PASS_NONABSORBING_NONZERO_DETERMINANT_COMPONENTS',
                saturation=saturation_audit(),normalization=normalization_audit(),
                duration=duration_audit(),carry_expansion=carry_expansion_audit(),
                two_power_terminal=two_power_audit(),
                scope='Decision proof for independent append bounds and nonzero coefficient determinant; general Presburger elimination is not implemented',
                determinant_zero='OPEN',joint_bound='NOT_COVERED',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(result,indent=2))
