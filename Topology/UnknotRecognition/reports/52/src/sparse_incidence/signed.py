"""Incidence refined by a binary orientation character.

The input rows are [a,b,c,d,sign,parity], where sign describes order reversal
and parity is a SEPARATE binary character. No assertion about surface
orientability is made unless the supplied parity is the actual character.
"""
from .api import analyze
from .geometry import prepare, natural
from .oracle import OrbitZetaOracle
from .reconstruct import ResourceExhausted
from .verify import verify


def lift_input(size, signed_rows, ports):
    raw, parity = [], []
    for row in signed_rows:
        if not isinstance(row, (list, tuple)) or len(row) != 6:
            raise ValueError('signed row must have six entries')
        if type(row[5]) is not int or row[5] not in (0,1):
            raise ValueError('parity must be zero or one, not bool')
        raw.append(row[:5]); parity.append(row[5])
    size, base, ports = prepare(size, raw, ports)
    cover = []
    for (a,b,c,d,sign), p in zip(base, parity):
        for sheet in (0,1):
            source, target = sheet*size, (sheet ^ p)*size
            cover.append((a+source,b+source,c+target,d+target,sign))
    cover_ports = [[(lo+sheet*size,hi+sheet*size)
                    for sheet in (0,1) for lo,hi in port] for port in ports]
    _, cover, cover_ports = prepare(2*size, cover, cover_ports)
    return size, base, ports, cover, cover_ports


def analyze_signed(size, signed_rows, ports, *, max_cycles=None, max_queries=None,
                   max_entries=None, check=None, record_certificate=False):
    size, base_rows, ports, cover_rows, cover_ports = lift_input(size, signed_rows, ports)
    base = analyze(size, base_rows, ports, max_cycles=max_cycles,
                   max_queries=max_queries, max_entries=max_entries, check=check,
                   record_certificate=record_certificate)
    if base['status'] != 'COMPLETE':
        return base
    remaining_cycles = None if max_cycles is None else max_cycles-base['stats']['cycles']
    remaining_queries = None if max_queries is None else max_queries-base['stats']['orbit_calls']
    oracle = OrbitZetaOracle(2*size, cover_rows, cover_ports,
        max_cycles=remaining_cycles, max_queries=remaining_queries,
        check=check, record_certificate=record_certificate)
    try:
        total = oracle.initialize()
        known = []
        for mask, weight in base['histogram']:
            oracle.check()
            # Every lifted component has exactly its base component's signature.
            value = oracle(mask)-sum(w for t,w in known if t & mask == t)
            if not weight <= value <= 2*weight:
                raise AssertionError('binary lift violates component bounds')
            known.append((mask,value))
        if sum(w for _,w in known) != total:
            raise AssertionError('cover support reconstruction lost mass')
        cover_certificate = oracle.certificate(known) if record_certificate else None
        typed = [[mask, v-w, 2*w-v]
                 for (mask,w), (_,v) in zip(base['histogram'],known)]
        cert = (dict(schema='signed-sparse-incidence-v1',
                     base=base['certificate'], cover=cover_certificate,
                     histogram=typed) if record_certificate else None)
        return dict(status='COMPLETE', histogram=typed, certificate=cert,
                    stats=dict(orbit_calls=base['stats']['orbit_calls']+oracle.stats['orbit_calls'],
                               cycles=base['stats']['cycles']+oracle.stats['cycles'],
                               base=base['stats'],cover=oracle.stats))
    except ResourceExhausted as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), histogram=None,
                    certificate=None,
                    stats=dict(orbit_calls=base['stats']['orbit_calls']+oracle.stats['orbit_calls'],
                               cycles=base['stats']['cycles']+oracle.stats['cycles']))


def verify_signed(size, signed_rows, ports, certificate, *, check=None):
    from .codec import decode
    size, base_rows, ports, cover_rows, cover_ports = lift_input(size, signed_rows, ports)
    cert = decode(certificate)
    if not isinstance(cert, dict) or cert.get('schema') != 'signed-sparse-incidence-v1':
        return False
    if not verify(size, base_rows, ports, cert.get('base'), check=check):
        return False
    if not verify(2*size, cover_rows, cover_ports, cert.get('cover'), check=check):
        return False
    base = dict(cert['base']['entries']); cover = dict(cert['cover']['entries'])
    if base.keys() != cover.keys():
        return False
    expected = [[m, cover[m]-w, 2*w-cover[m]] for m,w in base.items()]
    supplied = cert.get('histogram')
    if not isinstance(supplied, list) or len(supplied) != len(expected):
        return False
    for row in supplied:
        if (not isinstance(row,list) or len(row) != 3
                or any(type(v) is not int or v < 0 for v in row)):
            return False
    return supplied == expected and all(x >= 0 and y >= 0 for _,x,y in expected)
