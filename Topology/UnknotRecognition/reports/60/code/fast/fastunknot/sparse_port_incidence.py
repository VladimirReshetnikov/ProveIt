"""Sparse exact port-incidence inventories from one weighted AHT trace.

This is a polynomial-size alternative to the existing dense Boolean-lattice
interface. It records how many components have each occurring port mask;
an absent mask means zero. It does not encode boundary order or attachments.
"""

from .integer_codec import encoded_integer
from .interval_incidence import _prepare, _InvalidIncidence
from .weighted_orbits import (
    WeightInterval, weighted_orbit_counts, verify_weighted_orbit_certificate,
)


def _ports_and_weights(size, ports, max_ports, check):
    if max_ports is None:
        if not isinstance(ports, (list, tuple)):
            raise ValueError('ports must be an explicit list or tuple')
        max_ports = len(ports)
    size, ports = _prepare(size, ports, max_ports, check)
    dimension = len(ports)
    weights = []
    for index, intervals in enumerate(ports):
        check()
        basis = tuple(int(j == index) for j in range(dimension))
        for lo, hi in intervals:
            check()
            weights.append(WeightInterval(lo, hi, basis))
    return size, ports, weights


def _histogram(classes, check):
    counts = {}
    for item in classes:
        check()
        if any(value < 0 for value in item.value):
            raise ArithmeticError('indicator weights cannot become negative')
        mask = sum(1 << index for index, value in enumerate(item.value) if value)
        counts[mask] = counts.get(mask, 0) + item.multiplicity
    return [{'mask': mask, 'orbits': counts[mask]} for mask in sorted(counts)]


def sparse_port_incidence(size, pairings, ports, *, max_ports=None,
                          max_cycles=None, max_weight_blocks=None,
                          max_output_records=None, max_operations=None,
                          record_certificate=False,
                          check=None):
    """Count every occurring port signature, without allocating 2**r slots.

    Port intervals are half-open. Overlaps within a port are merged before
    assigning indicator weights, while overlaps across ports retain each bit.
    With resource caps disabled, complexity is polynomial in the encoded
    pairing system, interval count, port count and endpoint bit lengths.
    No geometry or knot-diagram provenance is inferred from these inputs.
    """
    poll = check if check is not None else lambda: None
    poll()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be boolean')
    size, normalized, weights = _ports_and_weights(size, ports, max_ports, poll)
    pairs = list(pairings)
    answer = weighted_orbit_counts(
        size, pairs, weights, dimension=len(normalized), max_cycles=max_cycles,
        max_weight_blocks=max_weight_blocks, max_output_records=max_output_records,
        max_operations=max_operations,
        check=poll, record_certificate=record_certificate)
    stats = dict(answer.stats, orbit_queries=1, orbit_cycles=answer.cycles)
    if not answer.complete:
        return dict(status='INCONCLUSIVE', reason=answer.reason, stats=stats)
    histogram = _histogram(answer.classes, poll)
    result = dict(status='COMPLETE', orbit_count=answer.orbits,
                  histogram=histogram, port_count=len(normalized), stats=stats)
    result['stats'].update(weight_profiles=len(answer.classes),
                           signature_records=len(histogram))
    if record_certificate:
        result['certificate'] = dict(
            schema='sparse-port-incidence-v1',
            ports=[[[lo, hi] for lo, hi in port] for port in normalized],
            orbit_count=answer.orbits, histogram=histogram,
            weighted=answer.certificate)
    poll()
    return result


class _MalformedPortCertificate(ValueError):
    pass


def _integer(value):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise _MalformedPortCertificate('invalid certificate integer') from exc


def verify_sparse_port_certificate(size, pairings, ports, certificate, *,
                                   max_ports=None, max_operations=None, check=None):
    """Reconstruct indicator weights and check the supplied weighted proof.

    The verifier never calls the orbit producer. Malformed certificates return
    False; malformed source inputs and callback exceptions propagate.
    """
    poll = check if check is not None else lambda: None
    poll()
    size, normalized, weights = _ports_and_weights(size, ports, max_ports, poll)
    fields = {'schema', 'ports', 'orbit_count', 'histogram', 'weighted'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'sparse-port-incidence-v1'):
        return False
    try:
        _, supplied, _ = _ports_and_weights(size, certificate['ports'], len(normalized),
                                            poll)
    except _InvalidIncidence:
        return False
    if supplied != normalized:
        return False
    if not verify_weighted_orbit_certificate(
            size, list(pairings), weights, certificate['weighted'],
            dimension=len(normalized), max_operations=max_operations, check=poll):
        return False
    # The weighted certificate's inventory has just been independently replayed.
    # Decode its public records and perform only a linear aggregation by mask.
    weighted = certificate['weighted']
    try:
        count = _integer(certificate['orbit_count'])
        claimed = certificate['histogram']
        if type(claimed) is not list:
            return False
        parsed = []
        for item in claimed:
            poll()
            if type(item) is not dict or set(item) != {'mask', 'orbits'}:
                return False
            mask, multiplicity = (_integer(item[name]) for name in ('mask', 'orbits'))
            if not 0 <= mask < (1 << len(normalized)) or multiplicity < 1:
                return False
            parsed.append({'mask': mask, 'orbits': multiplicity})
        classes = weighted['classes']
        counts = {}
        for item in classes:
            poll()
            value = tuple(_integer(x) for x in item[0])
            multiplicity = _integer(item[1])
            if len(value) != len(normalized) or any(x < 0 for x in value):
                return False
            mask = sum(1 << j for j, x in enumerate(value) if x)
            counts[mask] = counts.get(mask, 0) + multiplicity
        expected = [{'mask': mask, 'orbits': counts[mask]} for mask in sorted(counts)]
        return parsed == expected and count == sum(counts.values())
    except _MalformedPortCertificate:
        return False
