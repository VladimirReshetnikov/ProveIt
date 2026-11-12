"""Untrusted elaborators. No standalone checker imports this module.

Translate old native or one-context proofs to zero-normal seven-rule proofs,
then translate seven-rule proofs to the six-rule witness-switch calculus.
Proof trees may be duplicated. All outputs are checked by the target kernel.
"""
import copy
import upstream_native as native
import control_eight as old
import zero_seven as seven
import zero_six as six

Z = ['z']
V = ['v', 0]
SV = ['s', V]
ALIAS = ['i', ['s', Z], Z, Z]


def native_to_one(p):
    tag = p[0]
    if tag in ['hyp', 'zero', 'succ']:
        return copy.deepcopy(p)
    if tag == 'tr':
        _, a, b, major, minor = p
        major, minor = native_to_one(major), native_to_one(minor)
        return ['tr', b, major, ['tr', a, major, minor]]
    if tag in ['qe', 'de']:
        return [tag, p[1], native_to_one(p[2]), native_to_one(p[3])]
    if tag == 'di':
        return [tag, p[1], p[2], native_to_one(p[3])]
    if tag == 'qi':
        return [tag, p[1], native_to_one(p[2])]
    raise ValueError('Unknown native node')


def normalize(a):
    return seven.walk(a, lambda i, d: ['v', i])


def reflexivity(t):
    # IS at counter zero and a constant update gives a common source ending at t.
    p = ['succ', Z, Z, seven.shift(t)]
    return ['tr', V, p, p]


def normalize_proof(p):
    tag = p[0]
    if tag == 'hyp':
        return copy.deepcopy(p)
    if tag == 'zero':
        return reflexivity(normalize(p[1]))
    if tag == 'succ':
        return [tag, *(normalize(x) for x in p[1:])]
    if tag in ['tr', 'qe', 'de']:
        return [tag, normalize(p[1]), normalize_proof(p[2]), normalize_proof(p[3])]
    if tag == 'di':
        return [tag, normalize(p[1]), normalize(p[2]), normalize_proof(p[3])]
    if tag == 'qi':
        return [tag, normalize(p[1]), normalize_proof(p[2])]
    raise ValueError('Unknown one-context node')


def canonical_certificate(c, source='one'):
    (native if source == 'native' else old).check(c)
    p = native_to_one(c['proof']) if source == 'native' else c['proof']
    result = dict(variables=c['variables'], context=[normalize(a) for a in c['context']],
                  goal=normalize(c['goal']), proof=normalize_proof(p))
    seven.check(result)
    return result


def map_parameter(a, amount, protected=0):
    return seven.walk(a, lambda i, d:
                      ['v', i + amount if i >= d + protected else i])


def lift_proof(p, amount, local=0):
    """Weaken under amount new numerical variables and local assumptions.

    local records binders introduced by inference rules inside this proof;
    syntax binders and rule-parameter binders are protected separately.
    """
    tag = p[0]
    at = lambda a, extra=0: map_parameter(a, amount, local + extra)
    if tag == 'hyp':
        return [tag, p[1] + amount if p[1] >= local else p[1]]
    if tag == 'succ':
        return [tag, at(p[1]), at(p[2]), at(p[3], 1)]
    if tag == 'tr':
        return [tag, at(p[1], 1), lift_proof(p[2], amount, local),
                lift_proof(p[3], amount, local)]
    if tag == 'qe':
        return [tag, at(p[1]), lift_proof(p[2], amount, local),
                lift_proof(p[3], amount, local)]
    if tag == 'de':
        return [tag, at(p[1]), lift_proof(p[2], amount, local),
                lift_proof(p[3], amount, local + 1)]
    if tag == 'di':
        return [tag, at(p[1], 2), at(p[2]), lift_proof(p[3], amount, local + 1)]
    raise ValueError('Unknown six-rule node')


def replace_first_assumption(p, replacement, local=0):
    """Replace the first external assumption, preserving all other indices."""
    tag = p[0]
    if tag == 'hyp':
        return lift_proof(replacement, local) if p[1] == local else copy.deepcopy(p)
    if tag == 'succ':
        return copy.deepcopy(p)
    if tag in ['tr', 'qe']:
        return [tag, p[1], replace_first_assumption(p[2], replacement, local),
                replace_first_assumption(p[3], replacement, local)]
    if tag == 'de':
        return [tag, p[1], replace_first_assumption(p[2], replacement, local),
                replace_first_assumption(p[3], replacement, local + 1)]
    if tag == 'di':
        return [tag, p[1], p[2], replace_first_assumption(p[3], replacement, local + 1)]
    raise ValueError('Unknown six-rule node')


def transport(e, p, template):
    """Full equational replacement from two crossed one-context steps."""
    return ['tr', template[2], e, ['tr', template[1], e, p]]


def to_six_proof(p):
    tag = p[0]
    if tag in ['hyp', 'succ']:
        return copy.deepcopy(p)
    if tag in ['tr', 'qe', 'de']:
        return [tag, p[1], to_six_proof(p[2]), to_six_proof(p[3])]
    if tag == 'qi':
        e, premise = p[1], to_six_proof(p[2])
        matrix = seven.shift(['q', e])[1]
        return ['de', ['q', e], ['di', matrix, Z, premise], ['hyp', 0]]
    if tag == 'di':
        b, t, premise = p[1], p[2], to_six_proof(p[3])
        if b[0] != '=' or t != Z:
            return [tag, b, t, premise]
        alias_zero = ['succ', Z, Z, Z]
        # The extra external parameter is the fresh step variable z.
        base_template = seven.shift(['q', seven.sub(b, Z)])[1]
        base = transport(alias_zero, ['hyp', 0], base_template)
        converted = replace_first_assumption(premise, base)
        zero_alias = ['tr', V, reflexivity(ALIAS), alias_zero]
        successor_template = seven.sub(seven.shift(['d', b])[1], ['s', ['v', 1]])
        endpoint = transport(zero_alias, converted, successor_template)
        return [tag, b, ALIAS, endpoint]
    raise ValueError('Unknown seven-rule node')


def six_certificate(c):
    seven.check(c)
    result = dict(c, proof=to_six_proof(c['proof']))
    six.check(result)
    return result
