"""Finite sanity check, NOT a Lean/Rocq proof or an endpoint validation."""
import json

def verify(n):
    U = range(n)
    checked = valid = 0
    for mask in range(1 << (n*n)):
        R = lambda x, y: bool(mask & (1 << (n*x+y)))
        for am in range(1 << n):
            A = {x for x in U if am & (1 << x)}
            functional = all(sum(R(x,y) for y in U) <= 1 for x in A)
            for bm in range(1 << n):
                B = {y for y in U if bm & (1 << y)}
                support = all(any(x in A and R(x,y) for x in U) for y in B)
                cover = all(not any(R(x,y) for y in U) or
                            any(y in B and R(x,y) for y in U) for x in A)
                checked += 1
                if functional and support and cover:
                    valid += 1
                    assert B == {y for y in U if any(R(x,y) for x in A)}
    return {'domain_size': n, 'triples_checked': checked, 'satisfying_premises': valid}

if __name__ == '__main__':
    result = {'scope': 'finite relation/set sanity checks, not formal compilation',
              'positive_checks': [verify(n) for n in range(4)]}
    # No guard: support can be justified by an input outside A.
    A, B, R = set(), {1}, {(0,1)}
    assert all(any((x,y) in R for x in range(2)) for y in B)
    assert B != {y for x,y in R if x in A}
    # No functionality: collection need only select one of two outputs.
    A, B, R = {0}, {0}, {(0,0),(0,1)}
    assert all(any((x,y) in R for x in A) for y in B)
    assert all(any((x,y) in R for y in B) for x in A)
    assert B != {y for x,y in R if x in A}
    result['negative_controls'] = ['unguarded support', 'nonfunctional two-output relation']
    print(json.dumps(result, indent=2))
