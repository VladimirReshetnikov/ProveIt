"""Untrusted proof compiler; the full-normal checker imports none of this."""
import copy
import checker as kernel

Z = ['z']
V = ['v', 0]
ONE = ['s', Z]
SV = ['s', V]


def normalize(a):
    return kernel.walk(a, lambda i, d: ['v', i])


def map_parameter(a, amount, protected=0):
    return kernel.walk(a, lambda i, d:
                       ['v', i + amount if i >= d + protected else i])


def lift_proof(p, amount, local=0):
    """Add equally many new variables and assumptions, protecting local ones."""
    tag = p[0]
    at = lambda a, extra=0: map_parameter(a, amount, local + extra)
    if tag == 'hyp':
        return [tag, p[1] + amount if p[1] >= local else p[1]]
    if tag == 'refl':
        return [tag, at(p[1])]
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
    raise ValueError('Unknown full-normal node')


def replace_first_assumption(p, replacement, local=0):
    """Replace the first external hypothesis under a context of the same size."""
    tag = p[0]
    if tag == 'hyp':
        return lift_proof(replacement, local) if p[1] == local else copy.deepcopy(p)
    if tag == 'refl':
        return copy.deepcopy(p)
    if tag in ['tr', 'qe']:
        return [tag, p[1], replace_first_assumption(p[2], replacement, local),
                replace_first_assumption(p[3], replacement, local)]
    if tag == 'de':
        return [tag, p[1], replace_first_assumption(p[2], replacement, local),
                replace_first_assumption(p[3], replacement, local + 1)]
    if tag == 'di':
        return [tag, p[1], p[2], replace_first_assumption(p[3], replacement, local + 1)]
    raise ValueError('Unknown full-normal node')


def qcase(matrix, premise):
    unused_witness = kernel.shift(['q', matrix])[1]
    return ['de', ['q', matrix], ['di', unused_witness, ONE, premise], ['hyp', 0]]


def envelope(e):
    assert e[0] == '='
    gate = ['=', ['i', V, Z, kernel.shift(e[1], 2)],
            ['i', V, Z, kernel.shift(e[2], 2)]]
    return ['q', gate]


def raise_equation(proof, equation):
    return qcase(envelope(equation)[1], lift_proof(proof, 1))


def lower_envelope(proof):
    return ['qe', ONE, proof, ['refl', Z]]


def equation_case_zero(matrix, premise):
    """Recover atomic case introduction at zero by a compound Q envelope."""
    a = kernel.sub(['q', matrix], Z)[1]
    endpoint = kernel.sub(a, SV, 0)
    converted = replace_first_assumption(premise, lower_envelope(['hyp', 0]))
    major = ['di', envelope(matrix), Z, raise_equation(converted, endpoint)]
    shifted_matrix = kernel.shift(['d', matrix])[1]
    at_witness = kernel.sub(['q', shifted_matrix], V)[1]
    local_base = kernel.shift(kernel.sub(at_witness, Z))
    base_proof = raise_equation(['hyp', 0], local_base)
    step = lower_envelope(['qe', SV, ['hyp', 1], base_proof])
    minor = ['di', shifted_matrix, V, step]
    return ['de', ['d', matrix], major, minor]


def normalize_proof(p):
    """Compile zero-normal six-rule proofs, repairing any changed DI branch."""
    tag = p[0]
    if tag == 'hyp':
        return copy.deepcopy(p)
    if tag == 'succ':
        return ['refl', normalize(['i', ['s', p[1]], p[2], p[3]])]
    if tag == 'zero':
        return ['refl', normalize(p[1])]
    if tag in ['tr', 'qe', 'de']:
        return [tag, normalize(p[1]), normalize_proof(p[2]), normalize_proof(p[3])]
    if tag == 'di':
        b, t, premise = normalize(p[1]), normalize(p[2]), normalize_proof(p[3])
        if b[0] == '=' and t == Z and p[2] != Z:
            return equation_case_zero(b, premise)
        return [tag, b, t, premise]
    raise ValueError('Unknown input node')


def certificate(c):
    result = dict(variables=c['variables'],
                  context=[normalize(a) for a in c['context']],
                  goal=normalize(c['goal']), proof=normalize_proof(c['proof']))
    kernel.check(result)
    return result
