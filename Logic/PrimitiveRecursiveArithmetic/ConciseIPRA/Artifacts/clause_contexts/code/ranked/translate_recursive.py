"""Lossless translation between tagged terms and the recursive arity codec."""
from translate import term_forward, term_backward


def formula_forward(a):
    if a[0] == 'd':
        return ['d', formula_forward(a[1])]
    return [term_forward(a[1]), term_forward(a[2])]


def formula_backward(a):
    if a[0] == 'd':
        return ['d', formula_backward(a[1])]
    return ['=', term_backward(a[0]), term_backward(a[1])]


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
