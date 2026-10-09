"""Independent forward checker for sparse component-incidence certificates.

Does not import sparse_zeta, sparse_incidence, or the orbit producer.
It verifies atom masses, dominating zero sets, and final mass conservation.
Correctness uses nonnegativity, not an untrusted claimed sparsity bound.
"""
from .interval_orbit_verify import verify_orbit_certificate
from .sparse_incidence_common import (InvalidSparse, integer, prepare,
                                     selected_union, cone_rows, pairing_rows)


def verify_sparse_port_incidence_certificate(size, pairings, ports, certificate,
                                             *, max_ports=None, check=None):
    """Return False for malformed/false proofs; callback exceptions propagate.

    The caller must separately bind the interval system to its geometric
    source. This checker establishes no knot-exterior provenance or verdict.
    Work is polynomial in explicit proof size; impose I/O limits externally.
    """
    poll = check if check is not None else lambda: None
    try:
        return _verify(size, pairings, ports, certificate, max_ports, poll)
    except InvalidSparse:
        return False


def _verify(size, pairings, ports, cert, max_ports, poll):
    poll()
    size, ports = prepare(size, ports, max_ports, poll)
    rows = pairing_rows(size, pairings, poll)
    if not isinstance(cert, dict) or cert.get('format') != 'sparse-incidence-v1':
        return False
    if integer(cert.get('size')) != size:
        return False
    _, bound_ports = prepare(size, cert.get('ports'), max_ports, poll)
    if bound_ports != ports:
        return False
    base = cert.get('base')
    if not verify_orbit_certificate(size, rows, base, check=poll):
        return False
    total = integer(base['orbit_count'])
    if integer(cert.get('orbit_count')) != total:
        return False
    proofs, steps, histogram = (cert.get(key) for key in ('proofs', 'steps', 'histogram'))
    if not all(isinstance(value, list) for value in (proofs, steps, histogram)):
        return False
    full = (1 << len(ports)) - 1
    verified, union_owner, used = {}, {}, set()

    def mask(raw):
        value = integer(raw)
        if not 0 <= value <= full:
            raise InvalidSparse('mask leaves the port set')
        return value

    def zeta(allowed, ref):
        poll()
        marked = selected_union(ports, full ^ allowed, poll)
        if not marked:
            if ref is not None:
                raise InvalidSparse('empty union must use the implicit count')
            return total
        index = integer(ref)
        if not 0 <= index < len(proofs):
            raise InvalidSparse('invalid union-proof reference')
        record = proofs[index]
        if not isinstance(record, dict):
            raise InvalidSparse('invalid union-proof record')
        if index not in verified:
            _, declared = prepare(size, [record.get('union')], 1, poll)
            if declared[0] != marked or marked in union_owner:
                raise InvalidSparse('incorrect or duplicate union binding')
            trace = record.get('trace')
            if not verify_orbit_certificate(size, rows + cone_rows(marked), trace,
                                             check=poll):
                raise InvalidSparse('invalid coned orbit proof')
            value = integer(trace['orbit_count']) - 1
            if not 0 <= value <= total:
                raise InvalidSparse('impossible coned count')
            verified[index] = marked, value
            union_owner[marked] = index
        if verified[index][0] != marked:
            raise InvalidSparse('proof rebound to a different union')
        used.add(index)
        return verified[index][1]

    prior = []
    seen_masks = set()

    def forward(allowed):
        subtotal = 0
        for known_mask, known_count in prior:
            poll()
            if known_mask & allowed == known_mask:
                subtotal += known_count
        return subtotal

    for step in steps:
        poll()
        if not isinstance(step, dict):
            return False
        target, count = mask(step.get('mask')), integer(step.get('count'))
        if count <= 0 or target in seen_masks:
            return False
        if zeta(target, step.get('support_ref')) != forward(target) + count:
            return False
        zeros = step.get('zeros')
        if not isinstance(zeros, list):
            return False
        checked_bits = set()
        for witness in zeros:
            poll()
            if not isinstance(witness, (list, tuple)) or len(witness) != 3:
                return False
            bit, allowed = integer(witness[0]), mask(witness[1])
            if not 0 <= bit < len(ports) or bit in checked_bits:
                return False
            bitmask = 1 << bit
            if not target & bitmask or allowed & bitmask:
                return False
            proper = target ^ bitmask
            if proper & allowed != proper:
                return False
            if zeta(allowed, witness[2]) != forward(allowed):
                return False
            checked_bits.add(bit)
        if checked_bits != {bit for bit in range(len(ports)) if target & (1 << bit)}:
            return False
        prior.append((target, count))
        seen_masks.add(target)
    if sum(count for _, count in prior) != total or len(used) != len(proofs):
        return False
    decoded = []
    for term in histogram:
        poll()
        if not isinstance(term, (list, tuple)) or len(term) != 2:
            return False
        decoded.append((mask(term[0]), integer(term[1])))
    return decoded == sorted(prior)
