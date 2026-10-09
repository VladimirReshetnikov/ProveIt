"""Independent parity-cover replay; no producer or producer lift is imported.

Shares input/port schemas, but reconstructs the lift directly. MIT-0.
"""
from .sparse_incidence_verify import verify_sparse_port_incidence_certificate
from .sparse_incidence_common import InvalidSparse, integer, prepare, pairing_rows


def verify_signed_sparse_port_incidence_certificate(size, signed_pairings, ports,
                                                     certificate, *,
                                                     max_ports=None, check=None):
    poll = check if check is not None else lambda: None
    try:
        return _verify(size, signed_pairings, ports, certificate, max_ports, poll)
    except InvalidSparse:
        return False


def _verify(size, signed, ports, cert, max_ports, poll):
    poll()
    size, ports = prepare(size, ports, max_ports, poll)
    if not isinstance(signed, (list, tuple)) or not isinstance(cert, dict):
        return False
    if (cert.get('format') != 'signed-sparse-incidence-v1'
            or integer(cert.get('size')) != size):
        return False
    _, bound_ports = prepare(size, cert.get('ports'), max_ports, poll)
    if bound_ports != ports:
        return False
    normalized, base_rows, lifted_rows = [], [], []
    for item in signed:
        poll()
        if isinstance(item, (list, tuple)) and len(item) == 6:
            row, parity = item[:5], integer(item[5])
        elif hasattr(item, 'pairing') and hasattr(item, 'parity'):
            row, parity = item.pairing, integer(item.parity)
        else:
            return False
        if parity not in (0, 1):
            return False
        a, b, c, d, sign = pairing_rows(size, [row], poll)[0]
        normalized.append([a, b, c, d, sign, parity])
        base_rows.append([a, b, c, d, sign])
        # First copy starts in sheet 0; second copy starts in sheet 1.
        lifted_rows.append([a, b, c + parity * size, d + parity * size, sign])
        lifted_rows.append([a + size, b + size,
                            c + (1 - parity) * size, d + (1 - parity) * size, sign])
    bound = cert.get('signed_pairings')
    if (not isinstance(bound, list) or any(not isinstance(row, (list, tuple))
                                          or len(row) != 6 for row in bound)):
        return False
    if [[integer(x) for x in row] for row in bound] != normalized:
        return False
    lifted_ports = []
    for port in ports:
        poll()
        lifted_ports.append([(a, b) for a, b in port]
                            + [(a + size, b + size) for a, b in port])
    base, cover = cert.get('base'), cert.get('cover')
    if not verify_sparse_port_incidence_certificate(
            size, base_rows, ports, base, max_ports=max_ports, check=poll):
        return False
    if not verify_sparse_port_incidence_certificate(
            2 * size, lifted_rows, lifted_ports, cover,
            max_ports=max_ports, check=poll):
        return False
    b = {integer(mask): integer(count) for mask, count in base['histogram']}
    d = {integer(mask): integer(count) for mask, count in cover['histogram']}
    expected = []
    for mask in sorted(b.keys() | d.keys()):
        poll()
        c, lifted = b.get(mask, 0), d.get(mask, 0)
        if not c <= lifted <= 2 * c:
            return False
        expected.append([mask, lifted - c, 2 * c - lifted])
    claimed = cert.get('histogram')
    if (not isinstance(claimed, list) or any(not isinstance(row, (list, tuple))
                                            or len(row) != 3 for row in claimed)):
        return False
    return (integer(cert.get('orbit_count')) == integer(base['orbit_count'])
            and [[integer(x) for x in row] for row in claimed] == expected)
