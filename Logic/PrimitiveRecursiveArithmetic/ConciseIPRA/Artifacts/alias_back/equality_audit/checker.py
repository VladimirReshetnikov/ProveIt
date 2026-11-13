"""Strict checker for the equality-only Alias/Back fragment.

This is NOT the complete iPRA checker and is not a Lean formalization.
The extra pred constructor represents a schematic unary formula placeholder.
Free parameters are named; object-language bound variables use de Bruijn indices.
"""
import json
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def term(t, parameters, depth=0):
    require(type(t) is list and len(t) > 0, 'term must be a tagged list')
    tag = t[0]
    if tag == '0':
        require(len(t) == 1, 'zero arity')
    elif tag == 'v':
        require(len(t) == 2 and type(t[1]) is str and t[1] in parameters,
                'unavailable free parameter')
    elif tag == 'b':
        require(len(t) == 2 and type(t[1]) is int and 0 <= t[1] < depth,
                'out-of-scope bound variable')
    elif tag == 's':
        require(len(t) == 2, 'successor arity')
        term(t[1], parameters, depth)
    elif tag == 'i':
        require(len(t) == 4, 'iterator arity')
        term(t[1], parameters, depth)
        term(t[2], parameters, depth)
        term(t[3], parameters, depth + 1)
    else:
        raise ValueError('unknown term constructor')


def formula(a, parameters, depth=0):
    require(type(a) is list and len(a) > 0, 'formula must be a tagged list')
    tag = a[0]
    if tag == 'eq':
        require(len(a) == 3, 'equation arity')
        term(a[1], parameters, depth)
        term(a[2], parameters, depth)
    elif tag in ('q', 'd'):
        require(len(a) == 2, 'binder arity')
        formula(a[1], parameters, depth + (1 if tag == 'q' else 2))
    elif tag == 'pred':
        require(len(a) == 3 and type(a[1]) is str, 'predicate arity')
        term(a[2], parameters, depth)
    else:
        raise ValueError('unknown formula constructor')


def substitute(a, parameter, replacement):
    """One-pass free substitution; replacement is locally closed."""
    if type(a) is not list:
        return a
    if len(a) == 2 and a[0] == 'v' and a[1] == parameter:
        return replacement
    return [substitute(child, parameter, replacement) for child in a]


def derive(proof, context, parameters):
    require(type(proof) is dict, 'proof must be an object')
    rule = proof.get('rule')
    if rule == 'hyp':
        require(set(proof) == {'rule', 'index'}, 'hyp fields')
        i = proof['index']
        require(type(i) is int and 0 <= i < len(context), 'hyp index')
        return context[i]
    if rule == 'alias':
        require(set(proof) == {'rule', 'parameter', 'term', 'body'}, 'alias fields')
        b, t = proof['parameter'], proof['term']
        require(type(b) is str and b not in parameters, 'alias parameter not fresh')
        term(t, parameters)
        result = derive(proof['body'], context + [['eq', ['v', b], t]], parameters | {b})
        result = substitute(result, b, t)
        formula(result, parameters)
        return result
    if rule == 'back':
        require(set(proof) == {'rule', 'parameter', 'term', 'formula', 'equality', 'instance'},
                'back fields')
        b, t, a = proof['parameter'], proof['term'], proof['formula']
        require(type(b) is str and b in parameters, 'back source is not a parameter')
        term(t, parameters)
        formula(a, parameters)
        require(derive(proof['equality'], context, parameters) == ['eq', ['v', b], t],
                'back equality mismatch')
        require(derive(proof['instance'], context, parameters) == substitute(a, b, t),
                'back instance mismatch')
        return a
    raise ValueError('unknown proof rule')


def verify(data):
    require(type(data) is dict and set(data) == {'parameters', 'assumptions', 'goal', 'proof'},
            'certificate fields')
    p = data['parameters']
    require(type(p) is list and all(type(x) is str for x in p) and len(set(p)) == len(p),
            'parameter declaration')
    p = set(p)
    context = data['assumptions']
    require(type(context) is list, 'assumptions')
    for a in context:
        formula(a, p)
    formula(data['goal'], p)
    require(derive(data['proof'], context, p) == data['goal'], 'goal mismatch')


if __name__ == '__main__':
    verify(json.load(sys.stdin))
    print('ACCEPT')
