"""Complete45/46 native positive-trit word predicates with exact bounds."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from math import comb
from pathlib import Path
import sympy as sp
import native_controller_three_selector_53 as prior


OUTER = [('twice_nu','*',2,'nu'), ('index_lower','+','twice_nu',12),
         ('word_bound','+','r','alpha')]
OUTER45 = [('index_lower','+','nu',13), ('word_bound','+','r','alpha')]
CORE = [tuple('q' if item == 'n2' else item for item in row) for row in prior.CORE]


def source_check(implicit_parity=False):
    parameters = ['q','r']
    auxiliaries = [name for name in prior.CORE_NAMES if name != 'r']+['nu','alpha']
    z = {name:sp.Symbol(name) for name in parameters+auxiliaries}
    q,r = z['q'],z['r']
    a,c,d,f,h,i,j,k,o,s,w,tau,eta,zeta,ga,ya = (
        z[name] for name in prior.CORE_NAMES if name != 'r')
    X,Y = w*q,s*q
    Delta = a*a+6*a+8
    u = 2*r+1+j*c
    index_source = r-z['nu']-13 if implicit_parity else r-2*z['nu']-12
    sources = [index_source, r+z['alpha']-q,
               ((X*Y)**2+X)*(Y*k)**2-tau*(tau+1),
               c-Y*k-eta, k-eta-zeta, k-r-1-h*X*Y,
               a-Y*(X+1), d-X-a*c-ga*(6*a+8),
               d*d-1-Delta*c*c, (i*c*c)**2-Delta*(f*f-1),
               Delta*(f*f-1)*(u*u-ya*ya)-(1-ya*ya), u-c-o*f]
    equalities = [('r','index_lower'),('word_bound','q')]+prior.kernel.EQUALITIES[1:]
    schedule = (OUTER45 if implicit_parity else OUTER)+CORE
    env = prior.execute(schedule,z)
    records = []
    correction = sources[9]*(u*u-ya*ya)
    for index,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust = correction if index == 10 else 0
        assert sp.expand(env[left]-env[right]-source-adjust) == 0, index
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    total = 45 if implicit_parity else 46
    mults = 25 if implicit_parity else 26
    assert len(schedule) == total and counts['*'] == mults
    assert counts['+']+counts['-'] == 20 and len(equalities) == 12
    assert len(auxiliaries) == 18
    assert set().union(*(source.free_symbols for source in sources)) == set(z.values())
    return dict(operations=total,multiplications=mults,additions_subtractions=20,
                equations=12,positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records)


def prepower():
    count = nonpower = 0
    for q in range(15,201):
        for r in range(14,q):
            assert r >= 14 and q >= 15 and q > r
            assert q*q > r+1 and q*(q+1) > 2*r+1
            assert 12*r < q*(q+1)
            assert r+2 >= 16
            assert 3*9**r < q**(r+1)
            assert 4*q*(q*(q-1)-1)-11 > 0
            count += 1
            rem = q
            while rem % 3 == 0:
                rem //= 3
            nonpower += rem != 1
    return dict(arbitrary_scale_index_pairs=count,nonpower_scales=nonpower,
                minimum_scale=15,minimum_index=14,maximum_scale=200)


def words():
    count = accepted = canonical = 0
    for t in range(1,11):
        q = 3**t
        for r in range(1,q):
            arithmetic = r >= 14 and r % 2 == 0 and prior.valuation(r) >= t
            semantic = t >= 3 and r % 2 == 0 and r % 3 == 2 and prior.native(r,t)
            assert arithmetic == semantic, (t,r)
            count += 1
            if arithmetic:
                assert q <= 2*r-1 < r*r and prior.valuation(r) == t
                assert (r-12)//2 > 0 and r-13 > 0 and q-r > 0
                accepted += 1
        if t >= 3:
            for tail in product((1,2),repeat=t-1):
                r = 2+sum(bit*3**j for j,bit in enumerate(tail,1))
                if r % 2 == 0:
                    assert r >= 14 and prior.valuation(r) == t
                    canonical += 1
    assert accepted == canonical
    return dict(bounded_word_checks=count,admitted_words=accepted,
                independently_constructed_words=canonical,maximum_t=10)


def actual_kernel_examples():
    rows = []
    for q,r in ((27,14),(27,26)):
        X = 3**(2*r+1)
        Y = sum(comb(2*r,j)*X**(j-r) for j in range(r,2*r+1))
        assert X % q == Y % q == 0 and min(X//q,Y//q) > 0
        rows.append(dict(q=q,r=r,nu46=(r-12)//2,nu45=r-13,alpha=q-r,
                         scale_divisibility_verified=True,
                         main_first=prior.kernel.check_canonical_ratio(r)))
    return rows


def verify():
    return dict(status='PASS_COMPLETE_NATIVE_SINGLE_WORD_45_46',source=source_check(),
                source45=source_check(True),
                prepower=prepower(),words=words(),actual_kernel_examples=actual_kernel_examples(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
                established_complete_bound=76,
                scope='Exact even native word with unit2 and length>=3; no program mask, controller, input or acceptance.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:
        assert result == json.loads(receipt.read_text())
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','source45','actual_kernel_examples')},indent=2))
