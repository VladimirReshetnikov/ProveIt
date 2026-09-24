#!/usr/bin/env python3
"""Count two primary-source interfaces; neither is a replacement kernel.

The Pell congruence aliases show why its published exponential cutoff cannot
be omitted. The short cubic recognizes recurrence triples, not their index.
"""
from pathlib import Path
import json
import sympy as sp


def pell(a, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x+(a*a-1)*y, x+a*y
    return x, y


def verify():
    a, n, t, ell = sp.symbols('a n t ell')
    # Audited straight-line core: each row is one binary arithmetic operation.
    index_rows = [
        ('a2', '*', 'a', 'a'), ('disc', '-', 'a2', 1),
        ('am1', '-', 'a', 1), ('offset', '*', 'am1', 't'),
        ('y', '+', 'n', 'offset'), ('y2', '*', 'y', 'y'),
        ('dy2', '*', 'disc', 'y2'), ('rhs', '+', 'dy2', 1),
        ('ell2', '*', 'ell', 'ell')]
    def run(rows, initial):
        reg = dict(initial)
        for name, op, left, right in rows:
            assert name not in reg
            u = reg[left] if isinstance(left, str) else sp.Integer(left)
            v = reg[right] if isinstance(right, str) else sp.Integer(right)
            reg[name] = u*v if op == '*' else u+v if op == '+' else u-v
        return reg
    reg = run(index_rows, dict(a=a, n=n, t=t, ell=ell))
    assert sp.expand(reg['ell2']-reg['rhs']-
                     (ell**2-(a*a-1)*(n+(a-1)*t)**2-1)) == 0
    aliases = same_parity = 0
    for av in range(2, 17):
        cut, _ = pell(av, av)
        for nv in range(1, av):
            true_x, _ = pell(av, nv)
            assert true_x < cut
            for mult in range(1, 5):
                index = nv+mult*(av-1)
                xv, yv = pell(av, index)
                quotient, rem = divmod(yv-nv, av-1)
                assert rem == 0 and quotient > 0
                assert xv*xv-(av*av-1)*(nv+(av-1)*quotient)**2 == 1
                assert xv >= cut and index != nv and xv != true_x
                aliases += 1
                if index % 2 == nv % 2:
                    same_parity += 1

    x, y, z = sp.symbols('x y z')
    cubic = x**3+2*x*x*y+x*x*z+2*x*y*y-2*x*y*z-x*z*z+2*y**3-2*y*z*z+z**3
    cubic_rows = [
        ('x2', '*', 'x', 'x'), ('y2', '*', 'y', 'y'),
        ('z2', '*', 'z', 'z'), ('twoy', '*', 2, 'y'),
        ('s', '+', 'x', 'twoy'), ('xy2sum', '+', 'x2', 'y2'),
        ('first_gap', '-', 'xy2sum', 'z2'),
        ('first', '*', 's', 'first_gap'), ('second', '*', 'x', 'y2'),
        ('twoxy', '*', 'x', 'twoy'), ('second_gap', '-', 'x2', 'twoxy'),
        ('last_gap', '+', 'second_gap', 'z2'), ('third', '*', 'z', 'last_gap'),
        ('sum12', '+', 'first', 'second'), ('value', '+', 'sum12', 'third')]
    reg = run(cubic_rows, dict(x=x, y=y, z=z))
    assert sp.expand(reg['value']-cubic) == 0
    assert sp.expand(cubic.subs({x:y, y:z, z:x+y+z}, simultaneous=True)-cubic) == 0
    triple = (0, 0, 1)
    for _ in range(80):
        assert cubic.subs(dict(zip((x,y,z), triple))) == 1
        triple = (triple[1], triple[2], sum(triple))
    def count(rows):
        m = sum(row[1] == '*' for row in rows)
        return dict(multiplications=m, additions=len(rows)-m, total=len(rows))
    return dict(status='PASS_SCOPED_MODERN_KERNEL_INTERFACES',
                pell_index_core=count(index_rows), pell_index_rows=index_rows,
                wrong_index_aliases=aliases, same_parity_wrong_index_aliases=same_parity,
                cubic_orbit_core=count(cubic_rows), cubic_rows=cubic_rows,
                exact_cubic_identity=True, exact_cubic_recurrence_invariance=True,
                recurrence_triples=80,
                scope='Counts of the displayed cores only. The nine-operation Pell core omits its essential published exponential cutoff and is unsound as an exact-index predicate. The fifteen-operation cubic recognizes an orbit triple, without an exposed index, prime-power predicate, or binomial-divisibility predicate. No replacement of the proved43-operation kernel is established.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print({k:v for k,v in result.items() if not k.endswith('_rows')})
