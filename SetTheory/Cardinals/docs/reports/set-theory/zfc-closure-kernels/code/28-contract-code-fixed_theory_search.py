#!/usr/bin/env python3
"""Strict CP/GIC and EPSC2 refutation interfaces for the contraction kernel.

Main calibration: equality-free CP + all GIC instances, no IR. This is related
to upstream S0 by interpreting equality as the full observational profile.
Alternative: the EPSC2 schema from the incoming ProveIt EPSC2 proposal.

Candidates contain exactly {'matrices': [...], 'proof': [instructions...]};
they supply neither theory axioms nor a target. Only reconstructed BOT accepts.
Shortlex search is a complete mathematical reference search, not a TM compiler.
"""

from __future__ import annotations

from itertools import product
import json
from typing import Callable

import contraction_kernel as k


def Forall(name, formula):
    return k.All(k.close_name(formula, name))


def Exists(name, formula):
    return k.Not(Forall(name, k.Not(formula)))


def Or(a, b):
    return k.Imp(k.Not(a), b)


def NamedRel(a, b):
    return k.R(k.F(a), k.F(b))


def Subset(a, b, witness):
    return Forall(witness, k.Imp(NamedRel(witness, a), NamedRel(witness, b)))


def universal_closure(formula):
    for name in reversed(sorted(k.free_names(formula))):
        formula = Forall(name, formula)
    return formula


def cp_axiom():
    # Distinct local free helpers become bound indices during construction.
    p, v, x, w, y, z = range(-6, 0)
    powers = Exists(w, k.And(NamedRel(w, v),
                            Forall(y, k.Imp(Subset(y, x, z), NamedRel(y, w)))))
    closed = Forall(x, k.Imp(NamedRel(x, v), k.And(Subset(x, v, z), powers)))
    return Forall(p, Exists(v, k.And(NamedRel(p, v), closed)))


CP = cp_axiom()


def observational_equality(a, b):
    """Full incoming-and-outgoing profile; logical equality is not introduced."""
    lift = lambda v: k.B(v[1] + 1) if v[0] == 'b' else v
    aa, bb, z = lift(a), lift(b), k.B(0)
    incoming = k.All(k.Iff(k.R(z, aa), k.R(z, bb)))
    outgoing = k.All(k.Iff(k.R(aa, z), k.R(bb, z)))
    return k.And(incoming, outgoing)


def erase_equality(formula):
    """Syntactic translation of an ordinary formula with an extra ('eq',a,b) atom."""
    tag = formula[0]
    if tag == 'eq':
        return observational_equality(formula[1], formula[2])
    if tag in ('bot', 'rel'):
        return formula
    if tag == 'imp':
        return k.Imp(erase_equality(formula[1]), erase_equality(formula[2]))
    if tag == 'all':
        return k.All(erase_equality(formula[1]))
    raise ValueError('bad equality-bearing source formula')


def gic_axiom(matrix):
    matrix = k.freeze(matrix)
    if not k.scoped(matrix):
        raise ValueError('a GIC matrix must be locally closed')
    # Free 0 = input; free 1 = output; every other free name is a parameter.
    ceiling = max(k.free_names(matrix) | {0, 1}) + 1
    b, c, a, y, yp, x = range(ceiling, ceiling + 6)

    def at(input_name, output_name):
        return k.rename(matrix, lambda n: input_name if n == 0 else
                        output_name if n == 1 else n)

    selected = Exists(yp, k.And(at(a, yp), NamedRel(yp, c)))
    collect = Forall(a, k.Imp(NamedRel(a, b),
                             Forall(y, k.Imp(at(a, y), selected))))
    support = Forall(y, k.Imp(NamedRel(y, c), Exists(x, at(x, y))))
    return universal_closure(Forall(b, Exists(c, k.And(collect, support))))


# This exact projected wrapper is inherited from the incoming EPSC2 proposal
# checker/epsc2_tableau.py (ProveIt, docs/incoming/zfc_epsc2_proposal.zip).
# We materialize it into a separately bound/free-tagged syntax for this kernel.
def _br(i, j):
    return k.R(k.B(i), k.B(j))


def _hole(*projection):
    return ('hole',) + projection


def _ex(body):
    return k.Not(k.All(k.Not(body)))


_SB = k.All(_ex(k.All(k.Imp(_hole(2, 0, 4, 3),
                                k.All(k.Imp(_br(0, 1), _br(0, 2)))))))
_EMPTY = k.All(k.Not(_br(0, 1)))
_GUARD = Or(_EMPTY, _br(0, 1))
_CLOSED = k.All(k.Imp(_GUARD,
                      k.All(k.Imp(_hole(1, 0, 4, 3), _br(0, 2)))))
_SUPPORT = k.All(k.Imp(_br(0, 1), _ex(_hole(0, 1, 4, 3))))
EPSC2_TEMPLATE = k.All(k.All(k.Imp(_SB, _ex(k.And(_CLOSED, _SUPPORT)))))


def epsc2_axiom(matrix):
    matrix = k.freeze(matrix)
    if not k.scoped(matrix) or not k.free_names(matrix) <= {0, 1, 2, 3}:
        raise ValueError('EPSC2 matrices have exactly four available free slots')

    def expand(template):
        tag = template[0]
        if tag == 'hole':
            projection = template[1:]
            return k.edit(matrix, lambda var, d:
                          k.B(d + projection[var[1]]) if var[0] == 'f' else var)
        if tag in ('bot', 'rel'):
            return template
        if tag == 'imp':
            return k.Imp(expand(template[1]), expand(template[2]))
        return k.All(expand(template[1]))

    result = expand(EPSC2_TEMPLATE)
    if not k.scoped(result) or k.free_names(result):
        raise ValueError('internal EPSC2 wrapper scope failure')
    return result


def _fixed_refutation(certificate, *, alternative=False):
    if (not isinstance(certificate, dict) or set(certificate) != {'matrices', 'proof'}
            or not isinstance(certificate['matrices'], list)
            or not isinstance(certificate['proof'], list)):
        raise ValueError('candidate must contain exactly matrices and proof lists')
    matrices = certificate['matrices']
    if alternative:
        theory = [epsc2_axiom(m) for m in matrices]
    else:
        theory = [CP] + [gic_axiom(m) for m in matrices]
    lines = k.check_certificate({'instructions': certificate['proof']}, theory)
    if not lines or lines[-1] != k.BOT:
        raise ValueError('only reconstructed genuine falsity is a refutation')
    return {'accepted': True, 'theory': 'EPSC2' if alternative else 'CP+GIC',
            'schema_instances': len(matrices), 'proof_lines': len(lines)}


def check_refutation(certificate):
    """Main CP/GIC entry. CP is always axiom 0; matrix i gives GIC axiom i+1."""
    return _fixed_refutation(certificate)


def check_epsc2_refutation(certificate):
    """Alternative calibrated schema; matrix i gives EPSC2 axiom i."""
    return _fixed_refutation(certificate, alternative=True)


def shortlex_bytes_at(n: int) -> bytes:
    """The n-th finite byte word, by length then lexicographic order."""
    if not k.integer(n) or n < 0:
        raise ValueError('enumeration index must be a natural number')
    width, block = 0, 1
    while n >= block:
        n -= block
        width += 1
        block *= 256
    return n.to_bytes(width, 'big')


def index_of_bytes(data: bytes) -> int:
    if type(data) is not bytes:
        raise ValueError('a byte word is required')
    base = sum(256 ** length for length in range(len(data)))
    return base + int.from_bytes(data, 'big')


def decode_candidate(data: bytes):
    """Parse only data; JSON carries no executable expressions."""
    def reject_constant(_):
        raise ValueError('non-JSON numeric constants are not candidates')
    def decimal_integer(digits):
        # Avoid a host-configured decimal-digit cap becoming a logical bound.
        negative = digits.startswith('-')
        value = 0
        for digit in digits[int(negative):]:
            value = 10 * value + ord(digit) - ord('0')
        return -value if negative else value
    return json.loads(data.decode('utf-8'), parse_constant=reject_constant,
                      parse_int=decimal_integer)


def accepts_bytes(data: bytes, *, alternative=False) -> bool:
    """Mathematically total finite parser/checker, within host resource limits.

    Python RecursionError, MemoryError, interruption, and other resource failures
    propagate as errors. They are never converted into acceptance or rejection.
    """
    try:
        candidate = decode_candidate(data)
        _fixed_refutation(candidate, alternative=alternative)
        return True
    except (ValueError, TypeError, KeyError, UnicodeError):
        return False


def search(*, alternative=False):
    """Ideal shortlex refutation search; do not run expecting a finite answer.

    This defines a single fixed no-input algorithm. It returns iff an accepted
    certificate exists. It contains no time limit or heuristic rejection rule.
    """
    n = 0
    while True:
        if accepts_bytes(shortlex_bytes_at(n), alternative=alternative):
            return n
        n += 1


def direct_cp(domain: tuple, relation: Callable) -> bool:
    """Independent, literal semantic reading of the upstream CP sentence."""
    sub = lambda a, b: all(not relation(z, a) or relation(z, b) for z in domain)
    return all(any(relation(p, v) and all(
        not relation(x, v) or (sub(x, v) and any(
            relation(w, v) and all(not sub(z, x) or relation(z, w) for z in domain)
            for w in domain)) for x in domain) for v in domain) for p in domain)


def direct_gic(matrix, domain: tuple, relation: Callable) -> bool:
    """Independent semantic specification including universal parameter closure."""
    parameters = sorted(k.free_names(matrix) - {0, 1})
    for values in product(domain, repeat=len(parameters)):
        eta = dict(zip(parameters, values))

        def phi(a, y):
            assignment = lambda n: a if n == 0 else y if n == 1 else eta[n]
            return k.evaluate(matrix, domain, relation, assignment)

        for b in domain:
            witnesses = []
            for c in domain:
                collect = all(not relation(a, b) or all(
                    not phi(a, y) or any(phi(a, yp) and relation(yp, c) for yp in domain)
                    for y in domain) for a in domain)
                support = all(not relation(y, c) or any(phi(x, y) for x in domain)
                              for y in domain)
                witnesses.append(collect and support)
            if not any(witnesses):
                return False
    return True


def direct_epsc2(matrix, domain: tuple, relation: Callable) -> bool:
    """Independent literal reading of EPSC2, without a projected syntax wrapper."""
    sub = lambda a, b: all(not relation(z, a) or relation(z, b) for z in domain)
    empty = lambda a: all(not relation(z, a) for z in domain)
    for p, q in product(domain, repeat=2):
        def phi(x, y):
            assignment = {0: x, 1: y, 2: p, 3: q}.__getitem__
            return k.evaluate(matrix, domain, relation, assignment)
        bounded = all(any(all(not phi(x, y) or sub(y, b) for y in domain)
                          for b in domain) for x in domain)
        if not bounded:
            continue
        found = False
        for c in domain:
            closed = all(not ((empty(x) or relation(x, c)) and phi(x, y))
                         or relation(y, c) for x, y in product(domain, repeat=2))
            support = all(not relation(y, c) or any(phi(x, y) for x in domain)
                          for y in domain)
            if closed and support:
                found = True
                break
        if not found:
            return False
    return True


if __name__ == '__main__':
    print(json.dumps({'CP_closed': k.scoped(CP) and not k.free_names(CP),
                      'main_theory': 'equality-free CP + GIC, without IR',
                      'search_started': False}, indent=2))
