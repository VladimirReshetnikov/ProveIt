"""Fresh scalar corroboration; no source arrays or predecessor imports."""
from pathlib import Path
import argparse
import hashlib
import json
import math


def require(test, message):
    if not test:
        raise ValueError(message)


def prime(p):
    return p >= 2 and all(p % j for j in range(2, math.isqrt(p) + 1))


def half_sum_mod(R, p):
    # Direct integer-binomial recurrence for the defining upper half.
    r = (R - 1) // 2
    coefficient = math.comb(2 * r, r)
    power = 1
    total = 0
    modulus = 2 * p
    X = pow(2, R, modulus)
    for j in range(r + 1):
        total = (total + coefficient * power) % modulus
        if j < r:
            numerator = coefficient * (r - j)
            require(numerator % (r + j + 1) == 0, 'binomial division')
            coefficient = numerator // (r + j + 1)
            power = power * X % modulus
    require(total % 2 == 0, 'integral half')
    return total // 2


def homogeneous(h, a, b):
    return sum(math.comb(2*h-1, h+l) * a**l * b**(h-1-l)
               for l in range(h))


def valuation_factorial(n, p):
    result = 0
    while n:
        n //= p
        result += n
    return result


def geometric_mod(x, count, modulus):
    # Returns x**count and 1+...+x**(count-1), modulo modulus.
    if count == 0:
        return 1, 0
    power, total = geometric_mod(x, count // 2, modulus)
    square = power * power % modulus
    doubled = total * (1 + power) % modulus
    if count % 2:
        return square * x % modulus, (doubled + square) % modulus
    return square, doubled


def packet():
    records = []
    for p in range(3, 44, 2):
        if not prime(p):
            continue
        for e in range(1, 4):
            P = p**e
            if P > 180:
                continue
            for h in range(1, 8):
                for j in range(1, 6):
                    if P <= 2*j:
                        continue
                    R = 2*h*P - 2*j + 1
                    if R < 3:
                        continue
                    exponent = 2*h - 2*j + 1
                    a, b = 2**max(exponent, 0), 2**max(-exponent, 0)
                    xi = a * pow(b, -1, p) % p
                    Sh = sum(math.comb(2*h-1, h+l) * pow(xi, l, p)
                             for l in range(h)) % p
                    expected = (pow(xi, j, p) * pow((1+xi) % p, P-2*j, p)
                                * Sh * pow(2, -1, p)) % p
                    actual = half_sum_mod(R, p)
                    N = (a+b)*homogeneous(h, a, b)
                    require(actual == expected, 'Lucas residue')
                    require((actual == 0) == (N % p == 0), 'fixed-prime criterion')
                    records.append([p,e,h,j,R,actual,N % p])
    special = []
    for p in range(5, 44, 2):
        if not prime(p):
            continue
        for e in range(1, 4):
            P = p**e
            for h,j,numerator,denominator in [(1,2,1,27),(2,1,44,9)]:
                R = 2*h*P - 2*j + 1
                r = (R-1)//2
                central_depth = (valuation_factorial(2*r,p)
                                 - 2*valuation_factorial(r,p))
                require(central_depth == e, 'central carries')
                if P <= 180:
                    residue = half_sum_mod(R,p)
                    require(residue == numerator*pow(denominator,-1,p)%p,
                            'special residue')
                else:
                    residue = None
                special.append([p,e,h,j,R,central_depth,residue])
    shape = []
    for t in range(1, 5):
        d = 5**t
        B = 1 << d
        for n in range(1, 13):
            residues = []
            for p in [3,11]:
                Q = pow(2,d*n,p)
                _, total = geometric_mod(Q,B-1,p)
                residue = (1+total)%p
                require(residue != 0, 'short-period excluded prime')
                residues.append(residue)
            shape.append([d,n,*residues])
    deps = [
        Path('/tmp/direct_X_canonical_resonance_repair_aristotle.md'),
        Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md'),
        Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete83_gamma_small_prime_digit_rules.md')]
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    read_ends = [168,120,240]
    context=[]
    for dep,end in zip(deps,read_ends):
        lines=dep.read_bytes().splitlines(keepends=True)
        require(len(lines)>=end,'read span')
        context.append({'path':str(dep),'sha256':digest(dep),
                        'first_line':1,'last_line':end,
                        'read_span_sha256':hashlib.sha256(b''.join(lines[:end])).hexdigest()})
    return {
        'scope':'New scalar formula checks only; no authentic full compiler instances or source-array evaluation.',
        'note_sha256':digest(Path(__file__).with_suffix('.md')),
        'helper_sha256':digest(Path(__file__)),
        'dependencies':context,
        'direct_modular_binomial_cases':len(records),
        'max_direct_R':max(row[4] for row in records),
        'fixed_quotient_residues':records,
        'special_carry_cases':special,
        'short_family_modular_cases':shape,
        'not_claimed':['full zero','authentic outer resonance/slack solution',
                       'global impossibility for unbounded quotient h',
                       'prime-power sufficiency at exceptional primes',
                       'new paid operation count or universality']}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    result=packet()
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['direct_modular_binomial_cases','max_direct_R']}))
    print('special carry cases',len(result['special_carry_cases']))
    print('short-family modular cases',len(result['short_family_modular_cases']))


if __name__=='__main__':
    main()
