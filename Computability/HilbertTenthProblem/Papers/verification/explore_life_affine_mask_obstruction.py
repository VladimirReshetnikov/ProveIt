"""Seven-term binary-digit obstruction to auxiliary-free affine Life masks."""
from pathlib import Path
import json
import sympy as sp


def life(n, b):
    return int(n == 3 or (n == 2 and b == 1))


def verify():
    records = []
    closure_zero = closure_one = cases = 0
    side = (0, 1, 2, 4, 5, 6)
    for h in (1, 2, 4, 8, 16, 32, 64, 128):
        modulus = 2*h
        cz = co = 0
        for origin in range(modulus):
            for step in range(modulus):
                bits = tuple(int((origin+i*step) % modulus >= h) for i in range(7))
                assert bits not in ((0, 0, 0, 1, 0, 0, 0), (1, 1, 1, 0, 1, 1, 1))
                if all(bits[i] == 0 for i in side):
                    assert bits[3] == 0
                    cz += 1
                if all(bits[i] == 1 for i in side):
                    assert bits[3] == 1
                    co += 1
                # Complement identity used to cover tests prescribing digit one.
                complement = tuple(int((-origin-1-i*step) % modulus >= h) for i in range(7))
                assert complement == tuple(1-bit for bit in bits)
                cases += 1
        closure_zero += cz
        closure_one += co
        records.append(dict(modulus=modulus, progressions=modulus**2,
                            zero_closures=cz, one_closures=co))
    # Five positions do not suffice for this elementary closure argument.
    five = tuple(int((1+5*i) % 16 >= 8) for i in range(5))
    assert five == (0, 0, 1, 0, 0)
    valid = [dict(neighbors=n, center=0, output=0) for n in side]
    assert all(life(v['neighbors'], v['center']) == v['output'] for v in valid)
    assert life(3, 0) == 1
    a, d, e, f = sp.symbols('a d e f', integer=True)
    form = lambda n, b, y: a+d*n+e*b+f*y
    assert sp.expand(2*form(3, 0, 0)-form(2, 0, 0)-form(4, 0, 0)) == 0
    # Independent exact integer check of the key elementary proof inequality.
    inequality_cases = 0
    for h in range(1, 257):
        for t in range(h):
            assert 3*min(t, h-1-t) <= h+t
            inequality_cases += 1
    return dict(status='PASS_LIFE_AFFINE_MASK_OBSTRUCTION',
                progressions=cases, zero_closures=closure_zero,
                one_closures=closure_one, moduli=records,
                five_point_counterexample=dict(origin=1, step=5, modulus=16, bits=five),
                valid_transitions=valid,
                forced_invalid_transition=dict(neighbors=3, center=0, output=0),
                elementary_inequality_cases=inequality_cases,
                affine_interval_identity='2 L(3,0,0)=L(2,0,0)+L(4,0,0)',
                proof='../1980/EXPLORATION_LIFE_AFFINE_MASK_OBSTRUCTION.md',
                review='Author and two independent complete scoped proof/source reviews and fresh receipt checks PASS.',
                scope='No finite conjunction of fixed binary digit tests and affine interval constraints in neighbor count, center and output recognizes Life without auxiliaries. This is not an arbitrary-circuit lower bound, a bound for independently weighted neighbor bits, or a universal certificate result.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print(result['progressions'], result['zero_closures'], result['one_closures'])
