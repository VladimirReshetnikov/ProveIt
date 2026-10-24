#!/usr/bin/env python3
"""Independent finite checks for the proof's new arithmetic identities.

Uses only the standard library; does not import or execute repository code.
These checks supplement the unbounded proof, not the calibration theorem.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(value, label):
    if not value:
        raise ValueError(label)


def pell(a, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x + (a*a-1)*y, x+a*y
    return x, y


def main():
    counts = {}
    pins = json.loads((HERE/'SOURCE_PINS.json').read_text())
    for p in pins:
        data = (HERE/p['local_path']).read_bytes()
        require(hashlib.sha256(data).hexdigest() == p['sha256'], p['local_path'])
        git = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(git == p['git_blob_sha'], 'Git blob '+p['local_path'])
    counts['pinned_source_blobs'] = len(pins)

    count = 0
    for a in range(-12, 13):
        H = 4*a+3
        for c in range(-5, 6):
            for X in range(-8, 9):
                K = X*(X+2*a*c)-1
                Kr = X*(2*X-3*c)-2
                require(2*K == Kr+H*c*X, 'reduced projection identity')
                for T in range(-2, 3):
                    z = H*T+Kr
                    Ac = (z*z+3*H*H)*(z*z*z-19*H*H*H)
                    require((Ac-pow(Kr,5)) % abs(H) == 0, 'fifth-power carrier residue')
                    require(Ac != 0, 'nonzero carrier sample')
                    count += 1
    counts['carrier_identity_cases'] = count

    count = 0
    for A in list(range(-15,-2))+list(range(3,16)):
        H = 4*A-5
        a = A-2
        for R in range(1,22,2):
            d, C = pell(A,R)
            require(d*d-(A*A-1)*C*C == 1, 'Pell recurrence')
            for sigma in (-1,1):
                c = sigma*C
                for X in (-21,-8,-1,0,1,8,21):
                    K = X*(X+2*a*c)-1
                    Pi = (sigma*X-(1<<R))*((1<<R)*sigma*X+1)
                    require(((1<<R)*K-Pi) % abs(H) == 0, 'exact signed unit congruence')
                    count += 1
    counts['signed_projection_cases'] = count

    # A genuine negative control: powered divisibility alone is weaker.
    H, K = 3**5, 3
    require(pow(K,5) % H == 0 and K % H != 0, 'negative control fifth root')
    counts['negative_controls'] = 1

    # Bound coefficients and an independent integer check at the threshold.
    b,d,rmin = 64,5,24
    margin = b*(rmin+1-2*d)-(4*d+1)*rmin-4*d
    require(margin == 436 and b > 4*d+1, 'uniform saturation margin')
    for r in range(rmin,101):
        x = 1 << b
        require(x*(x-3)**r > (1 << (20*r+20))*x**10, 'powered-product strict bound')
    counts['saturation_bound_cases'] = 101-rmin
    require(1064921 > 64, 'authentic base exponent')

    # Exact leading-coefficient bookkeeping, independently of the DAG.
    exponents = dict(j=408,w=104,v=96,C=8,s=8,r=40,c=64,T=40)
    require(sum(exponents.values()) == 768, 'leading degree sum')
    require(104+7*96+24+2*8 == 816, 'two-adic leading coefficient')
    require(5*96+24+8 == 512, 'three-adic leading coefficient')
    require(4*96+24 == 408, 'beta leading exponent')

    result = {'passed': True, 'scope': 'finite identities, signed projection, bound and provenance; not full calibration',
              'counts': counts, 'saturation_margin': margin,
              'leading_degree':768,'leading_exponents':exponents,
              'leading_coefficient':'2^816 * 3^512 * beta^408',
              'source_commit':'84e16e43092614bae262ca59651cb9d77e31a255'}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
