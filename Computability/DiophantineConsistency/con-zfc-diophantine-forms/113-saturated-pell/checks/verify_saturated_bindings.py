#!/usr/bin/env python3
"""Bind the four literal positive circuits to the manuscript over free rings.

Each named mathematical register is checked as a complete sparse polynomial
in its local inputs. These checks compose in dependency order. Every live
arithmetic gate is covered; no numerical substitution is used here.
"""
import ast
from copy import deepcopy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def add(a, b, sign=1):
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, 0) + sign*c
        if not out[e]:
            del out[e]
    return out


def mul(a, b):
    out = {}
    for e, c in a.items():
        for f, d in b.items():
            ef = tuple(x+y for x, y in zip(e, f))
            out[ef] = out.get(ef, 0) + c*d
    return {e: c for e, c in out.items() if c}


def formulas(direct, sharp):
    bt = 'B' if direct else 'Bt'
    return [
        ('bJ', 'beta*J'), ('q', 'bJ+1'), ('C', 'q-F-alpha'),
        ('X', 'q+x' if direct else 'q*w'),
        ('k', 'eta+zeta'), ('c', 'Y*k+eta'), ('mu', 'q*q+1'),
        ('Am1', '(X+1)*Y*mu'), ('Hp', '4*Am1-1'),
        ('V0', 'X*mu*mu*Y*Y'), ('Dtau', '1+V0*(V0+1)*k*k'),
        ('G', 'bJ*(q-F)+alpha'),
        ('R', 'G*(q*q-1)+(MC+q*MF)*J'), ('e', 'k-R-1'),
        (bt, '(q*K0+X)*C-q*F' if direct else '(K0+w)*C-F'),
        ('U', 'c*c*i'), ('Delta', '(Am1+2)*Am1'),
        ('Cg', '(Am1+'+('1' if sharp else '2')+')*U*Dtau'),
        ('Df', '1+Delta*U*U*Dtau'),
        ('Q', 'Delta*Delta*U*U*Dtau'), ('delta', 'Q-1'),
        ('Tp', 'T+alpha'), ('V', '(c*Tp-R)*Df-c'),
        ('Dnum', 'Q*V*V-1'), ('L', 'Tp*k'),
        ('P1', ('q*q*q*q*bJ' if direct else 'q*q*q*bJ')),
        ('center', 'n+V+Cg-L*'+bt),
        ('Kpos', '3*X*c-2*X*X+2'),
        ('Zpart1', 'P1*mu*mu*(Hp*center+Kpos)'),
        ('inner', 'q*bJ*Y-q*q*q*B-bJ*X' if direct else 'bJ*Y-q*q*q*Bt'),
        ('Zpart2', 'Hp*(mu*mu*inner-P1*e)'),
        ('Znum', 'Zpart2+Zpart1'), ('Mtot', 'P1*mu*mu*Hp'),
        ('fg', 'delta*Mtot*Mtot*Dtau*Df'),
        ('fy', 'Mtot*Mtot*Dnum'), ('fs', 'delta*Znum*Znum'),
        ('N', '(fs-fg-fy)*(fs-fg-fy)-4*fg*fy')]


def check(packet):
    rows = {n: (op, a, b) for n, op, a, b in packet['source']}
    direct = 'x' in packet['witnesses']
    sharp = 'sharp' in packet['name']
    covered, verified = set(), set(packet['witnesses']+packet['fixed_numerals'])
    proofs = []
    for target, formula in formulas(direct, sharp):
        tree = ast.parse(formula, mode='eval').body
        refs = sorted({n.id for n in ast.walk(tree) if isinstance(n, ast.Name)})
        need(set(refs) <= verified, 'each formula uses previously verified registers')
        dimension = len(refs)
        zero = (0,)*dimension

        def integer(n):
            return {zero: n} if n else {}

        cache = {v: {tuple(int(i == j) for i in range(dimension)): 1}
                 for j, v in enumerate(refs)}

        def actual(name):
            if type(name) is int:
                return integer(name)
            if name in cache:
                return cache[name]
            need(name in rows, 'all free leaves bound for '+target+': '+name)
            covered.add(name)
            op, a, b = rows[name]
            a, b = actual(a), actual(b)
            value = mul(a, b) if op == '*' else add(a, b, -1 if op == '-' else 1)
            cache[name] = value
            return value

        def expected(n):
            if isinstance(n, ast.Name):
                return cache[n.id]
            if isinstance(n, ast.Constant):
                return integer(n.value)
            need(isinstance(n, ast.BinOp), 'ordinary polynomial syntax')
            a, b = expected(n.left), expected(n.right)
            return mul(a, b) if isinstance(n.op, ast.Mult) else add(a, b, -1 if isinstance(n.op, ast.Sub) else 1)

        left, right = actual(target), expected(tree)
        need(left == right, 'exact mathematical binding: '+target)
        verified.add(target)
        proofs.append({'register': target, 'free_inputs': refs, 'expanded_terms': len(right)})
    need(covered == set(rows), 'every literal arithmetic gate covered: '+str(set(rows)-covered))
    return {'name': packet['name'], 'all_arithmetic_gates_covered': len(covered),
            'complete_local_polynomial_identities': proofs}


def run():
    results = []
    for direct in (False, True):
        for sharp in (False, True):
            name = ('direct_' if direct else '')+'saturated_'+('sharp' if sharp else 'upper')
            packet = json.loads((ROOT/'equations'/(name+'.json')).read_text())
            results.append(check(packet))
    # Concrete independent controls: wrong norm sign and wrong direct q power.
    rejected = []
    for target in ('N', 'P1'):
        packet = json.loads((ROOT/'equations/direct_saturated_sharp.json').read_text())
        bad = deepcopy(packet)
        for row in bad['source']:
            if row[0] == target:
                if target == 'N':
                    row[1] = '+'
                else:
                    row[2] = 'q3'
        try:
            check(bad)
        except ValueError:
            rejected.append(target)
        else:
            raise ValueError('corruption not rejected: '+target)
    return {'status': 'PASS', 'circuits': results, 'rejected_corruptions': rejected,
            'scope': 'Complete local free-polynomial identities compose to bind every gate to the displayed formulas.'}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
