"""One Boolean Life helper, eight affine operations, and a mixed-mask component."""
from itertools import product
from pathlib import Path
import json
import random
import sympy as sp

LOCAL = [
    ('u8','*',8,'U'), ('j5','*',5,'J'),
    ('f0','+','S','j5'), ('F','+','f0','u8'),
    ('y8','*',8,'Y'), ('g0','-','F','B'),
    ('g1','-','g0','J'), ('G','+','g1','y8'),
]
PACK = [('p3','*','q','G'), ('p2','+','F','p3'),
        ('p2q','*','q','p2'), ('p1','+','U','p2q'),
        ('p1q','*','q','p1'), ('P0','+','B','p1q')]


def schedule(doubled):
    radix, a, b = (64,61,16) if doubled else (32,30,8)
    return LOCAL+PACK+([('P','*',2,'P0')] if doubled else [])+[
        ('q2','*','q','q'), ('L','*','q2','q2'), ('D0','*','L','q2'),
        ('jscaled','*',radix-1,'J'), ('jcheck','+','jscaled',1),
        ('lscaled','*',radix-1,'lam'), ('lcheck','+','lscaled',1),
        ('mc','*',b,'q2'), ('mi','+','mc',a), ('M','*','lam','mi'),
        ('gap','-','L','P' if doubled else 'P0'),
        ('Lm1','-','L',1), ('prod','*','gap','Lm1'), ('r','+','prod','M'),
    ]


def run(values, steps):
    env = dict(values)
    for name,op,left,right in steps:
        assert name not in env
        a = env[left] if isinstance(left,str) else left
        b = env[right] if isinstance(right,str) else right
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def count(steps):
    m = sum(op == '*' for _,op,_,_ in steps)
    return dict(operations=len(steps),multiplications=m,additions=len(steps)-m)


def source_checks():
    symbols = dict(zip(('S','B','Y','U','J','q','lam'),sp.symbols('S B Y U J q lam')))
    s,b,y,u,j,q,lam = [symbols[k] for k in symbols]
    result = []
    for doubled in (False,True):
        e = run(symbols,schedule(doubled))
        f = s+5*j+8*u
        g = s-b+4*j+8*u+8*y
        p0 = b+q*u+q*q*f+q**3*g
        radix,a,co = (64,61,16) if doubled else (32,30,8)
        p = 2*p0 if doubled else p0
        expected = dict(F=f,G=g,P0=p0,L=q**4,D0=q**6,
                        jcheck=(radix-1)*j+1,lcheck=(radix-1)*lam+1,
                        M=lam*(a+co*q*q),r=(q**4-p)*(q**4-1)+lam*(a+co*q*q))
        if doubled: expected['P']=p
        for name,value in expected.items(): assert sp.expand(e[name]-value) == 0
        result.append(dict(doubled=doubled,radix=radix,count=count(schedule(doubled)),
                           comparisons=len(expected),schedule=schedule(doubled),
                           equality_tests=[['jcheck','q'],['lcheck','q2']],
                           further_predicate='D0 divides binom(2*r,r); not a free equality or a paid kernel.'))
    assert count(LOCAL) == dict(operations=8,multiplications=3,additions=5)
    assert result[0]['count'] == dict(operations=28,multiplications=14,additions=14)
    assert result[1]['count'] == dict(operations=29,multiplications=15,additions=14)
    return dict(local=count(LOCAL),variants=result)


def life(n,b): return int(n == 3 or n == 2 and b == 1)


def local_checks():
    scalar=neighborhood=0
    maxima=[0,0]
    for n,b,y in product(range(9),range(2),range(2)):
        witnesses=[]
        for u in range(2):
            e=run(dict(S=n+b,B=b,Y=y,U=u,J=1),LOCAL)
            assert e['F'] == n+b+5+8*u
            assert e['G'] == n+4+8*u+8*y
            maxima=[max(maxima[0],e['F']),max(maxima[1],e['G'])]
            if (e['F'] & 8) == (e['G'] & 8) == 0: witnesses.append(u)
            scalar+=1
        assert witnesses == ([int(n+b >= 3)] if y == life(n,b) else [])
    for bits in product(range(2),repeat=9):
        n,b=sum(bits[:8]),bits[8]
        for y,u in product(range(2),repeat=2):
            e=run(dict(S=n+b,B=b,Y=y,U=u,J=1),LOCAL)
            accepted=(e['F'] & 8) == (e['G'] & 8) == 0
            assert accepted == (y == life(n,b) and u == int(n+b >= 3))
            neighborhood+=1
    assert maxima == [22,28]
    return dict(scalar_assignments=scalar,neighborhood_assignments=neighborhood,
                maxima=maxima,auxiliary_boolean_planes=1,unique_witness='u=[n+b>=3]')


def arbitrary_mask_checks():
    tests=overflows=0
    for width in range(1,9):
        L=1<<width
        for M in range(L):
            for P in range(L):
                r=(L-P)*(L-1)+M
                carries=P.bit_count()+M.bit_count()-(P+M).bit_count()
                overflow=P+M >= L
                v2=(P & -P).bit_length()-1 if P else 0
                expected=width+M.bit_count()-carries-(v2 if overflow else 0)
                assert r.bit_count() == expected
                assert (r.bit_count() == width+M.bit_count()) == ((P & M) == 0)
                if overflow: assert carries > 0
                tests+=1
                overflows+=overflow
    return dict(all_masks_and_words=tests,overflow_cases=overflows,widths=list(range(1,9)))


def pack(values,radix): return sum(value*radix**i for i,value in enumerate(values))


def mixed_checks():
    rng=random.Random(843)
    packed=zero_fields=0
    for doubled in (False,True):
        radix=64 if doubled else 32
        for size in range(1,13):
            q=radix**size
            J=(q-1)//(radix-1)
            lam=(q*q-1)//(radix-1)
            for sample in range(30):
                cells=[(rng.randrange(9),rng.randrange(2)) for _ in range(size)]
                if sample == 0: cells=[(0,0)]*size
                expected_y=[life(n,b) for n,b in cells]
                good_u=[int(n+b>=3) for n,b in cells]
                yy=expected_y[:]
                uu=good_u[:]
                if sample%3 == 1: yy[sample%size]^=1
                if sample%3 == 2: uu[sample%size]^=1
                values=dict(q=q,J=J,lam=lam,
                            S=pack([n+b for n,b in cells],radix),
                            B=pack([b for n,b in cells],radix),
                            Y=pack(yy,radix),U=pack(uu,radix))
                e=run(values,schedule(doubled))
                assert e['jcheck'] == q and e['lcheck'] == q*q
                P=e['P'] if doubled else e['P0']
                assert 0 <= P < e['L'] and 0 < e['M'] < e['L']
                assert e['D0'] == q**6
                accepted=e['r'].bit_count() == 6*size*(6 if doubled else 5)
                assert accepted == (yy == expected_y and uu == good_u)
                assert accepted == ((P & e['M']) == 0)
                assert e['M'].bit_count() == (12 if doubled else 10)*size
                if doubled: assert e['r']%2 == 1
                zero_fields+=any(values[name] == 0 for name in ('B','Y','U'))
                packed+=1
    # Pre-power range proofs must also tolerate admissible non-power q.
    bounds=nonpowers=0
    for radix,a,co in ((32,30,8),(64,61,16)):
        for j in (1,2,3,4,5,17,65):
            q=(radix-1)*j+1
            lam=(q*q-1)//(radix-1)
            L=q**4
            M=lam*(a+co*q*q)
            for P in (0,L//2,L-1):
                r=(L-P)*(L-1)+M
                assert 0 < M < L
                assert 64 <= q**3 < r < q**8 < 2*(q**3)**3
                assert q**12 > r+1 and q**12 > 2*r+1
                bounds+=1
                nonpowers+=q & (q-1) != 0
    return dict(packed_cases=packed,zero_field_cases=zero_fields,
                pre_power_bound_cases=bounds,nonpower_bound_cases=nonpowers,
                cells_per_word=list(range(1,13)))


def verify():
    return dict(status='PASS_LIFE_ONE_AUXILIARY_THRESHOLD_COMPONENT',source=source_checks(),
                local=local_checks(),arbitrary_mask=arbitrary_mask_checks(),mixed=mixed_checks(),
                proof='../1980/EXPLORATION_LIFE_THRESHOLD_MASKS.md',
                review='Author and two independent complete scoped proof/source reviews and fresh receipt checks PASS.',
                scope='Local eight-operation/two-bit-test predicate and conditional28/29-operation mixed-mask sources. Geometry, input, global pre-decoding bounds, positive adapters, torus convolution and the43-operation kernel are not included.')


if __name__ == '__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print(result['local'])
    print(result['arbitrary_mask'])
    print(result['mixed'])
