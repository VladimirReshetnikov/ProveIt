"""Untrusted independent named proof producer for crossed global rewriting.

The produced primitive proof trees contain no invocation of a derived rule,
theorem catalogue, or arithmetic evaluator. A checker imports none of this.
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path


serial = 0


def fresh(prefix):
    global serial
    serial += 1
    return prefix + '_' + str(serial)


def V(x):
    return ('v', x)


def S(x):
    return ('s', x)


def I(n, a, x, h):
    return ('i', n, a, x, h)


def E(s, t):
    return ('=', s, t)


def Q(x, a):
    return ('q', x, a)


def D(x, y, a):
    return ('d', x, y, a)


def C(n, a, b):
    return I(n, a, fresh('unused'), b)


def J(a):
    return I(0, a, fresh('wrap'), 0)


def subst(a, x, t):
    if a == 0:
        return 0
    tag = a[0]
    if tag == 'v':
        return t if a[1] == x else a
    if tag == 's':
        return S(subst(a[1], x, t))
    if tag == 'i':
        _, n, b, v, h = a
        return I(subst(n, x, t), subst(b, x, t), v,
                 h if v == x else subst(h, x, t))
    if tag == '=':
        return E(subst(a[1], x, t), subst(a[2], x, t))
    if tag == 'q':
        return a if a[1] == x else Q(a[1], subst(a[2], x, t))
    if tag == 'd':
        return a if x in a[1:3] else D(a[1], a[2], subst(a[3], x, t))
    raise ValueError(tag)


def fv(a):
    if a == 0:
        return set()
    tag = a[0]
    if tag == 'v':
        return {a[1]}
    if tag == 's':
        return fv(a[1])
    if tag == 'i':
        return fv(a[1]) | fv(a[2]) | (fv(a[4]) - {a[3]})
    if tag == '=':
        return fv(a[1]) | fv(a[2])
    if tag == 'q':
        return fv(a[2]) - {a[1]}
    if tag == 'd':
        return fv(a[3]) - set(a[1:3])
    raise ValueError(tag)


def term(a, env):
    if a == 0:
        return ['z']
    if a[0] == 'v':
        return ['v', env.index(a[1])]
    if a[0] == 's':
        return ['s', term(a[1], env)]
    if a[0] == 'i':
        return ['i', term(a[1], env), term(a[2], env),
                term(a[4], (a[3],) + env)]
    raise ValueError(a)


def formula(a, env):
    if a[0] == '=':
        return ['=', term(a[1], env), term(a[2], env)]
    if a[0] == 'q':
        return ['q', formula(a[2], (a[1],) + env)]
    if a[0] == 'd':
        return ['d', formula(a[3], (a[2], a[1]) + env)]
    raise ValueError(a)


def same(a, b):
    env = tuple(sorted(fv(a) | fv(b)))
    encode = formula if isinstance(a, tuple) and a[0] in ('=', 'q', 'd') else term
    return encode(a, env) == encode(b, env)


def replace_named(u, s, t):
    """Alpha-aware top-down rewriting, with globally distinct binder names."""
    if same(u, s):
        return t
    if u == 0 or u[0] == 'v':
        return u
    if u[0] == 's':
        return S(replace_named(u[1], s, t))
    if u[0] == 'i':
        # A globally fresh state name cannot be a free variable of s or t.
        if u[3] in fv(s) | fv(t):
            new = fresh('renamed')
            u = I(u[1], u[2], new, subst(u[4], u[3], V(new)))
        return I(replace_named(u[1], s, t), replace_named(u[2], s, t),
                 u[3], replace_named(u[4], s, t))
    raise ValueError(u)


def node(rule, goal, **kw):
    return dict(rule=rule, goal=goal, **kw)


def hyp(a):
    return node('hyp', a)


def compute(a):
    if a[0] != 'i':
        raise ValueError('Not an iterator')
    _, n, seed, state, body = a
    if n == 0:
        return node('zero', E(a, seed), seed=seed, state=state, body=body)
    if n[0] != 's':
        raise ValueError('Counter is neither zero nor a successor')
    rhs = subst(body, state, I(n[1], seed, state, body))
    return node('succ', E(a, rhs), counter=n[1], seed=seed, state=state, body=body)


def rw(p, q):
    if p['goal'][0] != '=' or q['goal'][0] != '=':
        raise ValueError('RW premises must be equations')
    _, s, t = p['goal']
    _, u, v = q['goal']
    return node('rw', E(v, replace_named(u, s, t)), major=p, minor=q)


def join(p, q):
    if not same(p['goal'][1], q['goal'][1]):
        raise ValueError('Join sources differ')
    result = rw(p, q)
    if not same(result['goal'], E(q['goal'][2], p['goal'][2])):
        raise ValueError('Root replacement is wrong')
    return result


def refl(a):
    p = compute(J(a))
    return join(p, p)


def sym(p):
    return join(refl(p['goal'][1]), p)


def trans(p, q):
    if not same(p['goal'][2], q['goal'][1]):
        raise ValueError('Transitivity middle terms differ')
    return join(q, sym(p))


def qe(p, t, q):
    _, y, b = p['goal']
    if not same(q['goal'], subst(b, y, 0)):
        raise ValueError('Wrong QE base')
    return node('qe', subst(b, y, t), target=t, major=p, minor=q)


def di(a, t, z, p):
    _, x, y, b = a
    opened = subst(b, x, t)
    if not same(p['goal'], subst(opened, y, S(V(z)))):
        raise ValueError('Wrong DI successor')
    return node('di', a, witness=t, eigen=z, premise=p)


def de(p, b, q):
    if b in fv(q['goal']):
        raise ValueError('Escaping DE witness')
    return node('de', q['goal'], major=p, eigen=b, continuation=q)


def with_name(a, finish):
    """Derive a fresh b=a and discharge b using the native paired binder."""
    x, y, z, b = (fresh(t) for t in ('name_x', 'name_y', 'name_z', 'name_b'))
    gate = E(C(V(y), a, V(x)), a)
    package = D(x, y, gate)
    witness = J(a)
    successor = subst(subst(gate, x, witness), y, S(V(z)))
    step = trans(compute(successor[1]), compute(witness))
    introduced = di(package, witness, z, step)
    resource = Q(y, subst(gate, x, V(b)))
    at_zero = subst(resource[2], y, 0)
    at_one = qe(hyp(resource), S(0), compute(at_zero[1]))
    equality = sym(join(compute(at_one['goal'][1]), at_one))
    if not same(equality['goal'], E(V(b), a)):
        raise ValueError('Naming failed')
    return de(introduced, b, finish(V(b), equality))


def congruence(p, h):
    _, s, t = p['goal']

    def finish(b, equality):
        bt = trans(equality, p)
        hb = h(b)
        left = rw(equality, refl(hb))
        right = rw(bt, refl(hb))
        if not same(left['goal'], E(hb, h(s))) or not same(right['goal'], E(hb, h(t))):
            raise ValueError('Fresh-source rewrite touched a passive parameter')
        return join(right, left)

    result = with_name(s, finish)
    if not same(result['goal'], E(h(s), h(t))):
        raise ValueError('Congruence target differs')
    return result


def nodes(a):
    if a == 0 or a[0] == 'v':
        return 1
    if a[0] == 's':
        return 1 + nodes(a[1])
    if a[0] == 'i':
        return 1 + nodes(a[1]) + nodes(a[2]) + nodes(a[4])
    raise ValueError(a)


def sized_congruence(p, h):
    """Isolate intended occurrences using a large transparent iterator term."""
    s, t = p['goal'][1:]
    size = nodes(h(V(fresh('size_hole'))))
    numeral = 0
    for _ in range(size + 1):
        numeral = S(numeral)
    marker = I(0, s, fresh('marker_state'), numeral)
    if nodes(marker) <= size:
        raise ValueError('The marker is not sufficiently large')
    marker_s = compute(marker)
    marker_t = trans(marker_s, p)
    hm = h(marker)
    left = rw(marker_s, refl(hm))
    right = rw(marker_t, refl(hm))
    if not same(left['goal'], E(hm, h(s))) or not same(right['goal'], E(hm, h(t))):
        raise ValueError('The marker did not isolate the designated occurrences')
    return join(right, left)


def cross(p, h, q):
    if not same(q['goal'][1], h(p['goal'][1])):
        raise ValueError('Crossed minor source differs')
    return join(congruence(p, h), q)


def transport(p, f, g, q):
    return cross(p, g, cross(p, f, q))


def sized_transport(p, f, g, q):
    first = join(sized_congruence(p, f), q)
    return join(sized_congruence(p, g), first)


def identity_induction(initial):
    x, y, z, b, u = (fresh(t) for t in ('ind_x', 'ind_y', 'ind_z', 'ind_b', 'ind_u'))
    loop = lambda k: I(k, initial, u, V(u))
    body = E(loop(V(y)), initial)
    current = E(loop(V(z)), initial)
    step = trans(compute(loop(S(V(z)))), hyp(current))
    introduced = di(D(x, y, body), 0, z, step)
    return de(introduced, b, hyp(Q(y, body)))


def proof(p, context, env, rw_tag='rw'):
    rule = p['rule']
    if rule == 'hyp':
        for i, a in enumerate(context):
            if same(a, p['goal']):
                return ['hyp', i]
        raise ValueError('Missing hypothesis: ' + repr(p['goal']))
    if rule == 'zero':
        return ['zero', term(p['seed'], env), term(p['body'], (p['state'],) + env)]
    if rule == 'succ':
        return ['succ', term(p['counter'], env), term(p['seed'], env),
                term(p['body'], (p['state'],) + env)]
    if rule == 'rw':
        premises = [proof(p['major'], context, env, rw_tag),
                    proof(p['minor'], context, env, rw_tag)]
        if rw_tag == 'tr':
            hole = fresh('abstracted_hole')
            template = replace_named(p['minor']['goal'][1],
                                     p['major']['goal'][1], V(hole))
            return ['tr', term(template, (hole,) + env), *premises]
        return [rw_tag, *premises]
    if rule == 'qe':
        return ['qe', term(p['target'], env), proof(p['major'], context, env, rw_tag),
                proof(p['minor'], context, env, rw_tag)]
    if rule == 'di':
        _, x, y, b = p['goal']
        opened = subst(b, x, p['witness'])
        progress = b[0] == '=' and p['witness'] == 0
        eta = V(p['eigen']) if progress else 0
        local = subst(opened, y, eta)
        return ['di', formula(b, (y, x) + env), term(p['witness'], env),
                proof(p['premise'], [local] + context, (p['eigen'],) + env, rw_tag)]
    if rule == 'de':
        _, x, y, b = p['major']['goal']
        local = Q(y, subst(b, x, V(p['eigen'])))
        return ['de', formula(p['goal'], env), proof(p['major'], context, env, rw_tag),
                proof(p['continuation'], [local] + context, (p['eigen'],) + env, rw_tag)]
    raise ValueError(rule)


def certificate(p, context=(), env=(), rw_tag='rw'):
    return {'variables': len(env), 'context': [formula(a, env) for a in context],
            'goal': formula(p['goal'], env), 'proof': proof(p, list(context), env, rw_tag)}


def cases(rw_tag):
    result = []

    def add(name, p, context=(), env=(), accept=True, goal=None):
        c = certificate(p, context, env, rw_tag)
        if goal is not None:
            c['goal'] = formula(goal, env)
        result.append((name, c, accept, p))

    one, two, three = S(0), S(S(0)), S(S(S(0)))
    add('root_reflexivity_zero', refl(0))
    add('root_symmetry_computation', sym(compute(J(one))))
    s, t = V('a'), V('b')
    eq = E(s, t)
    major = hyp(eq)
    h = lambda z: I(z, s, 'passive_state', s)
    add('fresh_alias_passive_occurrence', congruence(major, h), [eq], ('a', 'b'))
    add('large_marker_passive_occurrence', sized_congruence(major, h), [eq], ('a', 'b'))
    f = lambda z: I(z, s, 'left_state', S(V('left_state')))
    g = lambda z: I(t, z, 'right_state', I(V('right_state'), z, 'inner_state', V('inner_state')))
    minor = E(f(s), g(s))
    add('two_sided_transport', transport(major, f, g, hyp(minor)), [eq, minor], ('a', 'b'))
    add('large_marker_two_sided_transport', sized_transport(major, f, g, hyp(minor)), [eq, minor], ('a', 'b'))
    hs = lambda z: I(s, one, 'outer_state', I(V('outer_state'), z, 'inner_bound', S(V('inner_bound'))))
    add('fresh_alias_nested_binders', congruence(major, hs), [eq], ('a', 'b'))
    add('large_marker_nested_binders', sized_congruence(major, hs), [eq], ('a', 'b'))
    free = V('a')
    variable_major = hyp(E(free, 0))
    independent = I(one, one, 'bound_state', V('bound_state'))
    correct = rw(variable_major, refl(independent))
    add('bound_variable_is_not_free_source', correct, [E(free, 0)], ('a',))
    incorrect = E(independent, I(one, one, 'bound_state', 0))
    add('reject_capture_of_bound_variable', correct, [E(free, 0)], ('a',), False, incorrect)
    mixed = I(one, one, 'outer', I(V('outer'), free, 'inner', V('outer')))
    add('rewrite_free_parameter_below_binders', rw(variable_major, refl(mixed)), [E(free, 0)], ('a',))
    overlap = rw(hyp(E(two, one)), refl(three))
    add('top_down_overlapping_creation', overlap, [E(two, one)])
    add('reject_bottom_up_new_match', overlap, [E(two, one)], accept=False, goal=E(three, one))
    # A closed consequence, so the naming lemma is exercised without assumptions.
    numerical = compute(J(one))
    hn = lambda z: I(z, one, 'closed_state', S(V('closed_state')))
    add('closed_derived_congruence', congruence(numerical, hn))
    add('closed_large_marker_congruence', sized_congruence(numerical, hn))
    induction = identity_induction(one)
    add('used_hypothesis_progress', induction)
    wrong = certificate(induction, rw_tag=rw_tag)
    wrong['proof'][2][2] = ['s', ['z']]
    result.append(('reject_case_in_place_of_progress', wrong, False, induction))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('strict_certificates'))
    parser.add_argument('--checker', type=Path)
    parser.add_argument('--rw-tag', default='rw')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    records = []
    for name, c, accept, p in cases(args.rw_tag):
        path = args.output / (name + '.json')
        path.write_text(json.dumps(c, separators=(',', ':')) + '\n')
        record = {'name': name, 'expected_accept': accept, 'bytes': path.stat().st_size}
        if args.checker:
            run = subprocess.run([sys.executable, str(args.checker)], input=path.read_bytes(),
                                 capture_output=True, timeout=30)
            actual = run.returncode == 0 and run.stdout == b'ACCEPT\n'
            record.update(actual_accept=actual, matched=actual == accept)
            if actual != accept:
                record['stderr'] = run.stderr.decode(errors='replace')[-2000:]
        records.append(record)
    (args.output / 'manifest.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps(records, indent=2))
    if any(r.get('matched') is False for r in records):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
