"""Untrusted producers for finite Alias/Back proof schemas."""
from pathlib import Path
from copy import deepcopy
import json
from checker import substitute

ROOT = Path(__file__).resolve().parent
V = lambda x: ['v', x]
Z = ['0']
S = lambda x: ['s', x]
I = lambda n, a, h: ['i', n, a, h]
E = lambda s, t: ['eq', s, t]
P = lambda s: ['pred', 'F', s]
H = lambda i: {'rule': 'hyp', 'index': i}


def names(data):
    if type(data) is str:
        return {data}
    if type(data) is list:
        return set().union(*(names(x) for x in data)) if data else set()
    if type(data) is dict:
        return set().union(*(names(x) for x in data.values())) if data else set()
    return set()


def fresh(*data):
    occupied = names(list(data))
    index = 0
    while f'a{index}' in occupied:
        index += 1
    return f'a{index}'


def weaken(proof, cutoff, amount=1):
    """Insert assumptions after the original context, before local aliases."""
    result = deepcopy(proof)
    if result['rule'] == 'hyp':
        if result['index'] >= cutoff:
            result['index'] += amount
    elif result['rule'] == 'alias':
        result['body'] = weaken(result['body'], cutoff, amount)
    elif result['rule'] == 'back':
        result['equality'] = weaken(result['equality'], cutoff, amount)
        result['instance'] = weaken(result['instance'], cutoff, amount)
    return result


def alias(b, t, body):
    return {'rule': 'alias', 'parameter': b, 'term': t, 'body': body}


def back(b, t, a, equality, instance):
    return {'rule': 'back', 'parameter': b, 'term': t, 'formula': a,
            'equality': equality, 'instance': instance}


def reflexivity(t, context, parameters):
    b = fresh(t, context, parameters)
    return alias(b, t, H(len(context)))


def symmetry(s, t, equality, context, parameters):
    b = fresh(s, t, equality, context, parameters)
    extended = context + [E(V(b), s)]
    q = back(b, s, E(V(b), t), H(len(context)), weaken(equality, len(context)))
    r = back(b, t, E(t, V(b)), q, reflexivity(t, extended, parameters + [b]))
    return alias(b, s, r)


def transport(s, t, body, hole, equality, instance, context, parameters):
    """body[hole:=s], s=t |- body[hole:=t], for any raw formula body."""
    reverse = symmetry(s, t, equality, context, parameters)
    b = fresh(s, t, body, hole, reverse, instance, context, parameters)
    named_s = back(b, t, E(V(b), s), H(len(context)), weaken(reverse, len(context)))
    target = substitute(body, hole, V(b))
    named_formula = back(b, s, target, named_s, weaken(instance, len(context)))
    return alias(b, t, named_formula)


def certificate(parameters, assumptions, goal, proof):
    return {'parameters': parameters, 'assumptions': assumptions, 'goal': goal, 'proof': proof}


def build():
    output = ROOT / 'certificates'
    output.mkdir(exist_ok=True)
    x, y, z = V('x'), V('y'), V('z')
    bound = ['b', 0]
    complex_t = I(x, S(y), I(bound, z, S(['b', 0])))
    fixtures = {}
    fixtures['reflexivity_variable'] = certificate(['x'], [], E(x, x), reflexivity(x, [], ['x']))
    fixtures['reflexivity_raw_iterator'] = certificate(['x', 'y', 'z'], [], E(complex_t, complex_t),
                                                       reflexivity(complex_t, [], ['x', 'y', 'z']))
    ctx = [E(x, y)]
    fixtures['symmetry'] = certificate(['x', 'y'], ctx, E(y, x), symmetry(x, y, H(0), ctx, ['x', 'y']))
    ctx = [E(x, y), P(x)]
    fixtures['schematic_formula_transport'] = certificate(['x', 'y'], ctx, P(y),
        transport(x, y, P(V('hole')), 'hole', H(0), H(1), ctx, ['x', 'y']))
    body = ['d', E(I(['b', 0], V('hole'), ['b', 0]),
                   I(['b', 1], V('hole'), S(['b', 0])))]
    ctx = [E(complex_t, S(z)), substitute(body, 'hole', complex_t)]
    fixtures['transport_beneath_D_and_iterators'] = certificate(['x', 'y', 'z'], ctx,
        substitute(body, 'hole', S(z)),
        transport(complex_t, S(z), body, 'hole', H(0), H(1), ctx, ['x', 'y', 'z']))
    # Exercise the weakening compiler on actual proofs with local aliases.
    ctx = [E(x, y), P(y)]
    reverse = symmetry(x, y, H(0), ctx, ['x', 'y'])
    fixtures['transport_with_nested_equality_derivation'] = certificate(['x', 'y'], ctx, P(x),
        transport(y, x, P(V('hole')), 'hole', reverse, H(1), ctx, ['x', 'y']))
    # Genuine Back instance where its replacement contains the source parameter.
    ctx = [E(x, S(x)), P(S(x))]
    fixtures['self_occurring_replacement'] = certificate(['x'], ctx, P(x),
        back('x', S(x), P(x), H(0), H(1)))
    for name, data in fixtures.items():
        (output / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    return fixtures


if __name__ == '__main__':
    print(json.dumps({'generated': list(build())}, indent=2))
