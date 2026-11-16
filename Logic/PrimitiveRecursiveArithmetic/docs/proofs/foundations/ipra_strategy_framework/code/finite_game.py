"""Exact executable reference for finite bounded quantifier-game certificates.
Only checks finite samples; not a formal proof in iPRA.
"""
from dataclasses import dataclass
from typing import Callable, Tuple

@dataclass(frozen=True)
class Node:
    kind: str                     # leaf, any, all
    children: Tuple['Node', ...] = ()
    value: bool = False

@dataclass(frozen=True)
class Certificate:
    winner: bool
    chosen: int = -1
    children: Tuple['Certificate', ...] = ()

def construct(t: Node) -> Certificate:
    if t.kind == 'leaf':
        return Certificate(t.value)
    assert t.kind in ('any', 'all')
    cs = tuple(construct(x) for x in t.children)
    v = any(x.winner for x in cs) if t.kind == 'any' else all(x.winner for x in cs)
    owner = (t.kind == 'any')
    if v == owner:  # owner wins: choose first child with same winner
        i = next(k for k, c in enumerate(cs) if c.winner == v)
        return Certificate(v, i, (cs[i],))
    return Certificate(v, -1, cs)  # other side wins, must audit all moves

def verify(t: Node, c: Certificate) -> bool:
    if t.kind == 'leaf':
        return c.winner == t.value and c.chosen == -1 and not c.children
    if t.kind not in ('any', 'all'):
        return False
    owner = (t.kind == 'any')
    if c.winner == owner:
        return (0 <= c.chosen < len(t.children)
                and len(c.children) == 1
                and c.children[0].winner == c.winner
                and verify(t.children[c.chosen], c.children[0]))
    return (c.chosen == -1 and len(c.children) == len(t.children)
            and all(x.winner == c.winner and verify(n, x)
                    for n, x in zip(t.children, c.children)))

def contract(a: int, Q: int, Z: Callable[[int, int], int],
             E: Callable[[int, int, int], int],
             R: Callable[[int, int, int, int], bool]):
    """Return either finite witness table or finite counterstrategy."""
    for q in range(Q):
        successful = [z for z in range(Z(a, q))
                      if all(R(a, q, z, e) for e in range(E(a, q, z)))]
        if not successful:
            return False, (q, [next(e for e in range(E(a, q, z))
                                    if not R(a, q, z, e))
                               for z in range(Z(a, q))])
    return True, [next(z for z in range(Z(a, q))
                       if all(R(a, q, z, e) for e in range(E(a, q, z)))
                       ) for q in range(Q)]

if __name__ == '__main__':
    import itertools
    def trees(depth):
        if depth == 0: return [Node('leaf', value=False), Node('leaf', value=True)]
        base = trees(depth - 1)
        return [Node(kind, combo) for kind in ('all', 'any')
                for n in range(3) for combo in itertools.product(base, repeat=n)]
    tests = trees(2)
    for t in tests:
        c = construct(t)
        assert verify(t, c)
        expected = t.value if t.kind == 'leaf' else (
            any(construct(x).winner for x in t.children) if t.kind == 'any'
            else all(construct(x).winner for x in t.children))
        assert c.winner == expected
    for a in range(8):
        for Q in range(5):
            Z = lambda a,q: (a+q)%4
            E = lambda a,q,z: (a+z)%5
            R = lambda a,q,z,e: (a+q+z+e)%3 != 0
            ok, cert = contract(a,Q,Z,E,R)
            literal = all(any(all(R(a,q,z,e) for e in range(E(a,q,z)))
                              for z in range(Z(a,q))) for q in range(Q))
            assert ok == literal
            if ok:
                assert len(cert) == Q
                assert all(0 <= cert[q] < Z(a,q) and all(R(a,q,cert[q],e)
                           for e in range(E(a,q,cert[q]))) for q in range(Q))
            else:
                q, bad = cert
                assert q < Q and len(bad) == Z(a,q)
                assert all(0 <= bad[z] < E(a,q,z) and not R(a,q,z,bad[z])
                           for z in range(Z(a,q)))
    print(f'PASS: {len(tests)} bounded game trees plus 40 parameterized contracts')
