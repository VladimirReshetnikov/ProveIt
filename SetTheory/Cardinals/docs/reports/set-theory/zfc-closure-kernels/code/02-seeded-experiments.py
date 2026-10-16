"""Deterministic finite regression checks for the paper's constructions.

None of these finite checks proves an infinite-schema theory consistent,
proves PA-equiconsistency, or verifies a Turing-machine implementation.
"""
from __future__ import annotations
import json
import random
from pathlib import Path
from formulas import Formula, templates, expand, In, Eq, Hole, Bot, Imp, And, Or, Iff, Not, All, Ex


def evaluate(f: Formula, n: int, membership: int, relation: int,
             env: dict[str, int] | None = None) -> bool:
    env = {} if env is None else env
    o, a = f.op, f.args
    if o == 'in': return bool(membership & (1 << (env[a[0]] * n + env[a[1]])))
    if o == 'eq': return env[a[0]] == env[a[1]]
    if o == 'hole':
        j = env[a[1]] if a[1] else 0
        return bool(relation & (1 << (env[a[0]] * n + j)))
    if o == 'bot': return False
    if o == 'not': return not evaluate(a[0], n, membership, relation, env)
    if o in {'all', 'ex'}:
        vals = (evaluate(a[1], n, membership, relation, dict(env, **{a[0]: k})) for k in range(n))
        return all(vals) if o == 'all' else any(vals)
    p = evaluate(a[0], n, membership, relation, env)
    if o == 'imp': return not p or evaluate(a[1], n, membership, relation, env)
    if o == 'and': return p and evaluate(a[1], n, membership, relation, env)
    if o == 'or': return p or evaluate(a[1], n, membership, relation, env)
    if o == 'iff': return p == evaluate(a[1], n, membership, relation, env)
    raise ValueError(o)


def graph_audit() -> dict:
    graphs = seeds = support_checks = pointed_seeds = 0
    for n in range(1, 5):
        full = (1 << n) - 1
        for code in range(1 << (n*n)):
            graphs += 1
            rows = [(code >> (n*x)) & full for x in range(n)]
            image = [0] * (1 << n)
            for a in range(1, 1 << n):
                low = a & -a
                image[a] = image[a ^ low] | rows[low.bit_length()-1]
            for point in range(n):
                pointed_seeds += 1
                c = image[1 << point]
                while True:
                    d = c | image[c]
                    if d == c: break
                    c = d
                assert image[(1 << point) | c] & ~c == 0
                assert c & ~image[full] == 0
            for a in range(1 << n):
                seeds += 1
                c = 0
                while True:
                    d = c | image[a | c]
                    if d == c: break
                    c = d
                assert image[a | c] & ~c == 0
                assert c & ~image[full] == 0
                # Any closed set contains the computed positive reachability hull.
                for w in range(1 << n):
                    if image[a | w] & ~w == 0:
                        assert c & ~w == 0
                    # The guarded relation R'(x,y) := x in A and R(x,y)
                    # has global range image[A], so any ISI witness is exact.
                    support_checks += 1
                    if image[a] & ~w == 0 and w & ~image[a] == 0:
                        assert w == image[a]
    return {'directed_relations': graphs, 'relation_seed_pairs': seeds,
            'candidate_witness_checks': support_checks, 'maximum_domain': 4, 'point_seed_checks': pointed_seeds}


def members(x: int) -> list[int]:
    return [i for i in range(x.bit_length()) if (x >> i) & 1]


def subsets(x: int) -> list[int]:
    out, y = [0], x
    while y:
        out.append(y)
        y = (y-1) & x
    return out


def switch_outputs(x: int) -> list[int]:
    if x and x & (x-1) == 0:
        return [x.bit_length()-1]
    return subsets(x)


def switch_hull(root: int) -> set[int]:
    seen, stack = {root}, [root]
    while stack:
        x = stack.pop()
        for y in switch_outputs(x):
            if y not in seen:
                seen.add(y); stack.append(y)
    return seen


def hf_audit() -> dict:
    local_checks = hull_members = 0
    for root in range(4096):
        out = switch_outputs(root)
        b = (root.bit_length()-1) if root and root & (root-1) == 0 else root
        for y in out:
            assert y & ~b == 0  # actual subset-boundedness of every local fiber
            local_checks += 1
        w = switch_hull(root)
        for x in w:
            assert set(members(x)) <= w  # transitivity
            assert set(switch_outputs(x)) <= w
            hull_members += 1
    # All-subsets closure alone need not be transitive.
    naive = set(subsets(2))
    assert naive == {0, 2} and 1 not in naive and 1 in members(2)
    families = 0
    for a in range(1 << 16):
        d: set[int] = set()
        desired: set[int] = set()
        for x in members(a):
            d.update(subsets(x)); desired.update(members(x))
        decoded = {s.bit_length()-1 for s in d if s and s & (s-1) == 0}
        assert decoded == desired
        families += 1
    return {'HF_roots_checked': 4096, 'local_fiber_outputs_checked': local_checks,
            'hull_member_checks': hull_members, 'singleton_decoding_families': families,
            'naive_subset_closure_counterexample': {'root_code': 2, 'hull_codes': [0,2], 'missing_member_code': 1}}


def expansion_audit() -> dict:
    rng = random.Random(380000)
    variables = ['x', 'y', 'z']
    def gen(depth: int) -> Formula:
        if depth == 0 or rng.randrange(4) == 0:
            k = rng.randrange(4)
            x, y = rng.choice(variables), rng.choice(variables)
            return [lambda: In(x,y), lambda: Eq(x,y), lambda: Hole(x,y), Bot][k]()
        k = rng.randrange(8)
        if k < 4: return [Imp, And, Or, Iff][k](gen(depth-1), gen(depth-1))
        if k < 6: return [All, Ex][k-4](rng.choice(variables), gen(depth-1))
        return Not(gen(depth-1))
    for _ in range(4000):
        f = gen(5)
        n = rng.randrange(1, 4)
        membership, relation = rng.randrange(1 << (n*n)), rng.randrange(1 << (n*n))
        env = {v: rng.randrange(n) for v in variables}
        assert evaluate(f,n,membership,relation,env) == evaluate(expand(f),n,membership,relation,env)
    checks = 0
    for f in templates().values():
        for n in (1,2):
            for membership in range(1 << (n*n)):
                for relation in range(1 << (n*n)):
                    assert evaluate(f,n,membership,relation) == evaluate(expand(f),n,membership,relation)
                    checks += 1
    return {'random_formula_checks': 4000, 'template_model_checks': checks, 'random_seed': 380000}


def countermodels() -> dict:
    t = templates()
    # On a one-element domain the two binary relations exhaust all possible matrices.
    for r in (0,1):
        assert evaluate(t['Ext'],1,0,r)
        assert evaluate(t['ISI'],1,0,r)
        assert not evaluate(t['NE'],1,0,r)
    assert not evaluate(t['PIBI'],1,0,1)
    assert not evaluate(t['SIBI'],1,0,1)
    for r in (0,1):
        assert evaluate(t['Ext'],1,1,r) and evaluate(t['SBC'],1,1,r)
        assert evaluate(t['Ext'],1,0,r) and evaluate(t['Sep'],1,0,r)
        assert evaluate(t['TC_set'],1,0,r)
    assert not evaluate(t['Sep'],1,1,0)
    assert not evaluate(t['Power'],1,0,0)
    assert not evaluate(t['TC_root'],1,0,0)
    return {'Ext_plus_ISI_without_NE': 'one object, empty membership',
            'Ext_plus_SBC_without_Separation': 'one object, full membership',
            'Ext_plus_Separation_plus_TC_set_without_Power': 'one object, empty membership',
            'all_binary_matrices_checked_per_model': 2}

if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O: assertions implement these tests.')
    results = {'status': 'passed', 'scope': 'Finite regression checks; not PA proofs or machine verification.',
               'graphs': graph_audit(), 'hereditarily_finite': hf_audit(),
               'syntax': expansion_audit(), 'deletion_countermodels': countermodels()}
    path = Path(__file__).resolve().parents[1] / 'results' / 'experiments.json'
    path.write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))
