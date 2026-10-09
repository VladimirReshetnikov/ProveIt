"""Signature-resolved parity consistency using two sparse incidence calls.

An orbit is consistent when every closed walk has parity zero. Calling this
'orientability' requires geometric provenance for the supplied parity labels.
No geometry or knot verdict is inferred here. MIT-0.
"""
from .sparse_incidence import analyze_sparse_port_incidence
from .sparse_incidence_common import (InvalidSparse, integer, allowance,
                                     prepare, pairing_rows)


def signed_rows(size, signed_pairings, poll):
    if not isinstance(signed_pairings, (list, tuple)):
        raise InvalidSparse('signed pairings must be an explicit list or tuple')
    out = []
    for item in signed_pairings:
        poll()
        if isinstance(item, (list, tuple)) and len(item) == 6:
            row, parity = item[:5], integer(item[5])
        elif hasattr(item, 'pairing') and hasattr(item, 'parity'):
            row, parity = item.pairing, integer(item.parity)
        else:
            raise InvalidSparse('expected a SignedPairing or a six-entry row')
        if parity not in (0, 1):
            raise InvalidSparse('parity must be zero or one')
        out.append(pairing_rows(size, [row], poll)[0] + [parity])
    return out


def analyze_signed_sparse_port_incidence(size, signed_pairings, ports, *,
                                         max_ports=None, max_terms=None,
                                         max_cycles=None, max_orbit_queries=None,
                                         record_certificate=False, check=None):
    """Return [mask,consistent_count,inconsistent_count] rows.

    The baseline and double-cover calls SHARE cycle and query allowances.
    max_terms limits each sparse histogram separately. On any incomplete
    subcalculation, no histogram or certificate is published.
    """
    poll = check if check is not None else lambda: None
    poll()
    size, ports = prepare(size, ports, max_ports, poll)
    rows = signed_rows(size, signed_pairings, poll)
    for name, value in [('max_cycles', max_cycles), ('max_terms', max_terms),
                        ('max_orbit_queries', max_orbit_queries)]:
        allowance(value, name)
    base_pairs = [row[:5] for row in rows]
    cover_pairs = []
    for a, b, c, d, sign, parity in rows:
        for sheet in (0, 1):
            poll()
            source, target = sheet * size, (sheet ^ parity) * size
            cover_pairs.append([a + source, b + source, c + target, d + target, sign])
    cover_ports = []
    for port in ports:
        poll()
        cover_ports.append(list(port) + [(lo + size, hi + size) for lo, hi in port])
    common = dict(max_ports=max_ports, max_terms=max_terms,
                  record_certificate=record_certificate, check=poll)
    base = analyze_sparse_port_incidence(
        size, base_pairs, ports, max_cycles=max_cycles,
        max_orbit_queries=max_orbit_queries, **common)
    stats = dict(base=base['stats'], orbit_cycles=base['stats']['orbit_cycles'],
                 orbit_queries=base['stats']['orbit_queries'])
    if base['status'] != 'COMPLETE':
        return dict(status='INCONCLUSIVE', reason=base['reason'], stats=stats)
    cycles_left = None if max_cycles is None else max_cycles - stats['orbit_cycles']
    queries_left = (None if max_orbit_queries is None
                    else max_orbit_queries - stats['orbit_queries'])
    cover = analyze_sparse_port_incidence(
        2 * size, cover_pairs, cover_ports, max_cycles=cycles_left,
        max_orbit_queries=queries_left, **common)
    stats['cover'] = cover['stats']
    stats['orbit_cycles'] += cover['stats']['orbit_cycles']
    stats['orbit_queries'] += cover['stats']['orbit_queries']
    if cover['status'] != 'COMPLETE':
        return dict(status='INCONCLUSIVE', reason=cover['reason'], stats=stats)
    b, d = dict(base['histogram']), dict(cover['histogram'])
    histogram = []
    for mask in sorted(b.keys() | d.keys()):
        poll()
        count, lifted = b.get(mask, 0), d.get(mask, 0)
        if not count <= lifted <= 2 * count:
            raise ArithmeticError('parity-cover signature counts are inconsistent')
        histogram.append([mask, lifted - count, 2 * count - lifted])
    result = dict(status='COMPLETE', histogram=histogram,
                  orbit_count=base['orbit_count'], stats=stats)
    if record_certificate:
        result['certificate'] = dict(
            format='signed-sparse-incidence-v1', size=size, ports=ports,
            signed_pairings=rows, histogram=histogram,
            orbit_count=base['orbit_count'], base=base['certificate'],
            cover=cover['certificate'])
    poll()
    return result
