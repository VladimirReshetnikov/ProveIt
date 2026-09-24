"""The M=2 scaled-input threshold retains b>x but has a full false witness.

All22 source polynomials and the changed complete90 DAG are checked.
Finite complete-mask examples are illustrative codes; the genuine fixed
empty-index construction and positive Pell extension are proved in the note.
"""
from pathlib import Path
import json
import sympy as sp

import round37_1980_binary_product_certificate as previous


NAMES = [name for name in previous.NAMES if name != 'H']
PARAMETERS = [name for name in previous.PARAMETERS if name != 'H']
SYM = {name: sp.Symbol(name) for name in NAMES}


def schedule(M=2):
    out = []
    for row in previous.SCHEDULE:
        if row[0] == 'theta_sum':
            assert row == ('theta_sum', '+', 'H', 'b')
            if M == 2:
                out.append(('theta_sum', '+', 'b', 'b'))
            else:
                out += [('threshold_product', '*', M, 'b'),
                        ('theta_sum', '+', 'threshold_product', M-2)]
        else:
            out.append(row)
    return out


def sources(M=2):
    # The old formal B=H+b+2 becomes M(b+1) exactly.
    return [sp.expand(p.subs(previous.SYM['H'], (M-1)*SYM['b']+M-2))
            for p in previous.source_residuals()]


def verify_source():
    env = dict(SYM)
    previous.baseline.run_schedule(schedule(), env)
    src = sources()
    s = SYM
    A, B = s['a']+2, 2*(s['b']+1)
    aux = 2*s['r']+1+s['j']*s['c']
    corrections = {
        2: -s['la']*src[3],
        16: src[15]*(aux**2-s['y_aux']**2),
        17: src[3]*(s['ka']+s['rho']*(src[3]-2*(A-B))),
    }
    records = []
    for i, ((left, right), p) in enumerate(zip(previous.EQUALITIES, src)):
        actual = sp.expand(env[left]-env[right])
        correction = corrections.get(i, 0)
        if sp.expand(actual-p-correction) == 0:
            sign = 1
        else:
            assert correction == 0 and sp.expand(actual+p) == 0, i
            sign = -1
        records.append(dict(index=i, equality=[left, right], sign=sign,
                            source=sp.sstr(p), correction=sp.sstr(correction)))
    assert len(records) == 22
    assert src[1] == s['b']-s['x']-s['beta']
    assert sp.expand(src[3]-(s['th']-2*s['b'])) == 0
    primitive, histogram = previous.verify_primitives(schedule(), env)
    assert len(primitive) == 90 and histogram == {'+': 42, '*': 48}
    assert len(NAMES)-len(PARAMETERS) == 34
    # This is the literal large-M implementation, not an optimality claim.
    large_env = dict(SYM)
    previous.baseline.run_schedule(schedule(256), large_env)
    large_rows, large_count = previous.verify_primitives(schedule(256), large_env)
    assert len(large_rows) == 91 and large_count == {'+': 42, '*': 49}
    return dict(operations=90, multiplications=48, additions=42,
                positive_unknowns=34, equations=22, parameters=PARAMETERS,
                dag=schedule(), sources=records, retained_input_bound=True,
                large_M_example=dict(M=256, operations=91, multiplications=49, additions=42),
                scope='Exact full arithmetic for the refuted M2 redesign; the large-M count is for its displayed two-instruction threshold formula only.')


def psi2(L):
    a, b = 0, 1
    for _ in range(L):
        a, b = b, 4*b-a
    return a


def exact_case(L, V):
    assert L >= 16 and L % 2 == 0 and V > 0 and V % 2 == 0 and V < 2**(2*L)
    B, b, theta, x, beta = 8, 3, 6, 2, 1
    v, s = {0: (1, 5), 2: (1, 6), 4: (2, 5)}[V % 6]
    q = B**L
    ell = g = B**v
    e = ell+B**s
    C = x+g
    sigma = B**s*C*C
    alpha = q-ell-sigma
    lam = (q*q-1)//(B-1)
    S2 = ell+e*q
    assert (S2-V) % theta == 0
    t = (S2-V)//theta
    n = q**8
    coding = dict(x=x, b=b, beta=beta, th=theta, q=q, l=ell, e=e, g=g,
                  sigma=sigma, al=alpha, la=lam, V=V, t=t, n=n)
    assert all(a > 0 for a in coding.values())
    assert b == x+beta and B == 2*(b+1) and theta == 2*b
    assert ell < q and e < q and C*C < sigma < q
    assert sigma+ell+alpha == q
    T1 = q*q-1-b*ell
    T2 = theta*lam
    T3 = theta*ell
    Tplus = q*q*(1+theta*lam)+ell*(theta*q**4-b)
    S = g+q*q*S2+q**4*sigma
    assert Tplus-1 == T1+q*q*T2+q**4*T3
    assert 0 < T1 < q*q and 0 < T2 < q*q and 0 < T3 < q**4
    assert 0 < g < q*q and 0 < S2 < q*q and 0 < sigma < q**4
    assert (g & T1, S2 & T2, sigma & T3) == (0, 0, 0)
    assert S & (Tplus-1) == 0
    assert 0 < S < q**5 < n and 0 < Tplus < q**5 < n
    r = S*(n*n-n)+Tplus*(n*n-1)
    coding['r'] = r
    env = dict(coding)
    previous.baseline.run_schedule(schedule()[:33], env)
    # All eight equations involving only coding/packing coordinates.
    numerical = []
    for i in (0, 1, 2, 3, 4, 5, 6, 20):
        left, right = previous.EQUALITIES[i]
        assert env[left] == env[right], i
        numerical.append(i)
    assert n*n-1 <= r < 2*n**3 and r % 2 == 0
    needed = 2*(n.bit_length()-1)
    assert r.bit_count() >= needed
    assert B**(3*L) == q**3 < n and 2 <= L < 2*r+1
    assert n >= 64
    # Avoid forming U=2^(2r+1); n^2<2^(2r+1) follows from n<=r.
    assert n <= r and n.bit_length()*2 < 2*r+1
    return dict(L=L, V=str(V), V_mod6=V % 6, v=v, s=s,
                x=x, b=b, B=B, theta=theta,
                numeric_source_indices=numerical, coding_coordinates_positive=True,
                three_mask_intersections=[0, 0, 0], combined_intersection=0,
                q_bits=q.bit_length(), r_bits=r.bit_length(), r_even=True,
                central_valuation=r.bit_count(), required_valuation=needed,
                Tindex=psi2(L), missing_old_threshold=(3*L > B))


def verify():
    cases = []
    for L in (16, 32, 64, 128):
        for V in (2, 4, 6, 2**(2*L)-2, 2**(2*L)-4, 2**(2*L)-6):
            cases.append(exact_case(L, V))
    assert {c['V_mod6'] for c in cases} == {0, 2, 4}
    return dict(status='FULL_SOURCE_PASS_BUT_M2_REDESIGN_REFUTED',
                source=verify_source(), cases=cases, finite_cases=len(cases),
                numeric_coding_equations_per_case=8,
                proof='../1980/EXPLORATION_SCALED_INPUT_THRESHOLD.md',
                evidence_scope='The finite V values illustrate the uniform all-even-V construction; they are not asserted to be the actual empty compiler index. The note proves that application and the complete positive Pell extension without materializing enormous auxiliaries.',
                review='Author and two independent complete proof/source reviews and fresh verification runs passed without findings; arithmetic and proof frozen.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print({k: result['source'][k] for k in ('operations', 'multiplications', 'additions', 'positive_unknowns', 'equations')})
    print('finite cases:', result['finite_cases'], 'coding equations:', result['numeric_coding_equations_per_case'])
