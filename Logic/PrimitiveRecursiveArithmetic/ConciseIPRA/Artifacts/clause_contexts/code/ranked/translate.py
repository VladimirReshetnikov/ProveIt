"""Bijection between tagged Eq/D syntax and ranked, arity-coded syntax."""


def term_forward(a):
    if type(a) is int:
        return a
    return [term_forward(t) for t in a[1:]]


def term_backward(a):
    if type(a) is int:
        return a
    return ['s' if len(a) == 1 else 'i'] + [term_backward(t) for t in a]


def formula_forward(a):
    rank = 0
    while a[0] == 'd':
        rank += 1
        a = a[1]
    return [rank, term_forward(a[1]), term_forward(a[2])]


def formula_backward(a):
    rank, s, t = a
    result = ['=', term_backward(s), term_backward(t)]
    for unused in range(rank):
        result = ['d', result]
    return result


def proof_forward(p):
    tag = p[0]
    if tag == 'u':
        return [tag, p[1], term_forward(p[2]), [proof_forward(q) for q in p[3]]]
    if tag == 'x':
        return [tag, proof_forward(p[1]), proof_forward(p[2])]
    if tag == 'e':
        return [tag, formula_forward(p[1]), proof_forward(p[2]), proof_forward(p[3])]
    return [tag, formula_forward(p[1]), term_forward(p[2]), proof_forward(p[3])]


def proof_backward(p):
    tag = p[0]
    if tag == 'u':
        return [tag, p[1], term_backward(p[2]), [proof_backward(q) for q in p[3]]]
    if tag == 'x':
        return [tag, proof_backward(p[1]), proof_backward(p[2])]
    if tag == 'e':
        return [tag, formula_backward(p[1]), proof_backward(p[2]), proof_backward(p[3])]
    return [tag, formula_backward(p[1]), term_backward(p[2]), proof_backward(p[3])]


def forward(certificate):
    return {'goal': formula_forward(certificate['goal']),
            'proof': proof_forward(certificate['proof'])}


def backward(certificate):
    return {'goal': formula_backward(certificate['goal']),
            'proof': proof_backward(certificate['proof'])}
