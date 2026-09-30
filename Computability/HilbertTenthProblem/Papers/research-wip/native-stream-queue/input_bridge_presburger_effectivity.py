"""Effective periodic/power postprocessing; NOT a full Presburger eliminator."""
import argparse
from math import gcd, lcm
from pathlib import Path
import json


def polynomial(coefficients, n):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*n+coefficient
    return value


def truth(formula, n):
    kind, *parts = formula
    if kind == 'and':
        return all(truth(child,n) for child in parts)
    if kind == 'or':
        return any(truth(child,n) for child in parts)
    if kind == 'not':
        return not truth(parts[0],n)
    if kind == 'le':
        return polynomial(parts[0],n) <= 0
    if kind == 'eq':
        return polynomial(parts[0],n) == 0
    if kind == 'div':
        modulus, coefficients = parts
        return modulus != 0 and polynomial(coefficients,n) % abs(modulus) == 0
    raise ValueError(kind)


def parameters(formula):
    kind, *parts = formula
    if kind in ('and','or','not'):
        children = [parameters(child) for child in parts]
        return max([1]+[n for n,_ in children]), lcm(1,*[m for _,m in children])
    if kind == 'div':
        return 1, abs(parts[0]) or 1
    coefficients = list(parts[0])
    while coefficients and coefficients[-1] == 0:
        coefficients.pop()
    cutoff = 1 if len(coefficients) <= 1 else 2+sum(map(abs,coefficients[:-1]))//abs(coefficients[-1])
    return cutoff, 1


def periodic_data(formula):
    cutoff, period = parameters(formula)
    residues = [r for r in range(period)
                if truth(formula,cutoff+(r-cutoff)%period)]
    small = [n for n in range(1,cutoff) if truth(formula,n)]
    return dict(cutoff=cutoff,period=period,residues=residues,small=small)


def first_power(data, base=3):
    assert base >= 2
    n, exponent = 1, 0
    while n < data['cutoff']:
        if n in data['small']:
            return exponent
        n *= base
        exponent += 1
    seen = set()
    residue = n % data['period']
    while residue not in seen:
        if residue in data['residues']:
            return exponent
        seen.add(residue)
        residue = base*residue % data['period']
        exponent += 1
    return None


def width_formula(x):
    # U=(1,-1), V=(0,6), K=0: x-L+3L*A0+(6-3L)*A1=0.
    return ['and', ['le',[x+1,-1]], ['le',[3,-1]],
            ['or', ['and',['div',2,[0,1]],['div',6,[-x,1]]],
                   ['and',['not',['div',2,[0,1]]],['div',3,[-x,1]]]]]


def witness(x, width):
    if width <= x or width < 3:
        return None
    positive, negative, rhs = 3*width, 3*width-6, width-x
    divisor = gcd(positive,negative)
    if rhs % divisor:
        return None
    modulus = positive//divisor
    append1 = (-rhs//divisor*pow(negative//divisor,-1,modulus)) % modulus
    if append1 == 0:
        append1 += modulus
    append0 = (rhs+negative*append1)//positive
    assert append0 > 0 and append1 > 0
    assert x-width+3*width*append0+(6-3*width)*append1 == 0
    return append0, append1


def verify():
    arbitrary = [
        ['le',[1]], ['le',[-1]], ['eq',[0]], ['eq',[-9,0,1]],
        ['div',0,[0]], ['div',8,[-5,1]], ['div',9,[0,1]],
        ['and',['le',[-25,0,1]],['div',2,[-1,1]]],
        ['or',['le',[20,-2]],['div',12,[1,-2,1]]],
        ['not',['and',['le',[7,-3,1]],['div',6,[0,1,1]]]],
    ]
    rows = []
    periodic_checks = witness_checks = 0
    for formula in arbitrary+[width_formula(x) for x in range(1,25)]:
        data = periodic_data(formula)
        for n in range(1,max(100,data['cutoff']+3*data['period'])):
            encoded = n in data['small'] if n < data['cutoff'] else n%data['period'] in data['residues']
            assert encoded == truth(formula,n)
            periodic_checks += 1
        answer = first_power(data)
        brute = next((e for e in range(40) if truth(formula,3**e)),None)
        assert answer == brute
        rows.append(dict(formula=formula,periodic=data,first_ternary_power_exponent=answer))
    for x in range(1,25):
        data = periodic_data(width_formula(x))
        assert (first_power(data) is not None) == (x%3 == 0)
        for width in range(1,81):
            values = witness(x,width)
            assert truth(width_formula(x),width) == (values is not None)
            witness_checks += 1
    return dict(status='PASS_EFFECTIVE_PERIODIC_POWER_POSTPROCESSOR',
                full_presburger_quantifier_elimination_implemented=False,
                mathematical_effectivity_audit='Goodrick 1604.06166v2 Theorems1.4/1.5; BGW1608.08520v2 Steps1-4, specialized to parameter-only sentences.',
                formula_count=len(rows),periodic_checks=periodic_checks,
                exact_two_append_witness_checks=witness_checks,examples=rows,
                scope='Executable evidence covers only explicit final-form postprocessing and one hand-eliminated matrix family; generic elimination effectivity is a proof audit.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:
        assert result == json.loads(receipt.read_text(encoding='utf-8'))
    print({k:v for k,v in result.items() if k != 'examples'})
