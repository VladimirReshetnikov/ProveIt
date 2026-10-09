"""Independent sparse proof checking: no discovery or orbit producer imports.

The only shared mathematical code is public input normalization. Marked unions
are reconstructed by an endpoint sweep, and coning rows are rebuilt here.
The separately pinned upstream checker replays local orbit relations.
"""
from .codec import decode
from .geometry import prepare
from .kernels import load_kernel

class _Reject(Exception):
    pass

def _nat(value):
    if type(value) is not int or value < 0:
        raise _Reject('nonnegative integer required')
    return value

def _prepare(size, rows, ports):
    try:
        return prepare(size, rows, ports)
    except (ValueError, TypeError, IndexError):
        raise _Reject('malformed geometry') from None

def _union_by_sweep(ports, mask, check):
    events = {}
    for i, port in enumerate(ports):
        check()
        if (mask >> i) & 1:
            for lo, hi in port:
                events[lo] = events.get(lo, 0)+1
                events[hi] = events.get(hi, 0)-1
    active = 0
    start = None
    answer = []
    for point in sorted(events):
        before = active
        active += events[point]
        if before == 0 and active > 0:
            start = point
        if before > 0 and active == 0:
            answer.append((start, point))
    return tuple(answer)

def _cone(union):
    rows = []
    first = union[0][0]
    for left, right in union:
        last = right-1
        if left < last:
            rows.append((left,last-1,left+1,last,1))
        if left > first:
            rows.append((first,first,left,left,1))
    return tuple(rows)

def verify(size, pairings, ports, certificate, *, check=None):
    """Return False for a malformed/false proof; callback exceptions propagate.

    Parsing and replay have cost polynomial in the supplied data, not a hostile
    input memory guarantee. Apply serialized-size limits before JSON parsing.
    """
    checkpoint = check if check is not None else lambda: None
    checkpoint()
    try:
        return _verify(size, pairings, ports, decode(certificate), checkpoint)
    except _Reject:
        return False

def _verify(size, pairings, ports, cert, check):
    size, rows, ports = _prepare(size, pairings, ports)
    if not isinstance(cert, dict) or cert.get('schema') != 'sparse-incidence-v1':
        raise _Reject('unsupported certificate')
    if _nat(cert.get('size')) != size:
        raise _Reject('universe mismatch')
    csize, crows, cports = _prepare(cert['size'], cert.get('pairings'), cert.get('ports'))
    if crows != rows or cports != ports:
        raise _Reject('input binding mismatch')
    # Reject noncanonical certificate geometry, including reordered ports.
    if cert['pairings'] != [list(row) for row in rows]:
        raise _Reject('noncanonical pairing binding')
    if cert['ports'] != [[list(x) for x in p] for p in ports]:
        raise _Reject('noncanonical port binding')
    replay = load_kernel('interval_orbit_verify').verify_orbit_certificate
    if not replay(size, list(rows), cert.get('baseline'), check=check):
        raise _Reject('invalid baseline orbit proof')
    total = _nat(cert.get('total'))
    if total != _nat(cert['baseline'].get('orbit_count')):
        raise _Reject('total differs from baseline')
    full = (1 << len(ports))-1
    raw_entries = cert.get('entries')
    if not isinstance(raw_entries, list):
        raise _Reject('missing entries')
    entries = []
    for row in raw_entries:
        check()
        if not isinstance(row, list) or len(row) != 2:
            raise _Reject('bad histogram row')
        mask, weight = map(_nat, row)
        if mask > full or weight == 0:
            raise _Reject('invalid mask or zero weight')
        entries.append((mask, weight))
    if entries != sorted(entries, key=lambda row: (row[0].bit_count(), row[0])):
        raise _Reject('noncanonical support order')
    if len(set(m for m,w in entries)) != len(entries):
        raise _Reject('duplicate support')
    records = cert.get('union_proofs')
    if not isinstance(records, list):
        raise _Reject('missing union proofs')
    proof_table = {}
    for record in records:
        check()
        if not isinstance(record, dict):
            raise _Reject('invalid union proof record')
        _, _, parsed = _prepare(size, (), [record.get('union')])
        union = parsed[0]
        if (not union or record['union'] != [list(x) for x in union]
                or union in proof_table):
            raise _Reject('noncanonical or duplicate union')
        proof_table[union] = record.get('proof')
    used = {}

    def zeta(mask):
        check()
        union = _union_by_sweep(ports, full ^ mask, check)
        if not union:
            return total
        if union not in used:
            if union not in proof_table:
                raise _Reject('missing required union proof')
            proof = proof_table[union]
            if not replay(size, list(rows + _cone(union)), proof, check=check):
                raise _Reject('invalid coned orbit proof')
            value = _nat(proof.get('orbit_count'))-1
            if not 0 <= value <= total:
                raise _Reject('invalid coned orbit count')
            used[union] = value
        return used[union]

    empty = entries[0][1] if entries and entries[0][0] == 0 else 0
    if zeta(0) != empty:
        raise _Reject('wrong unmarked mass')
    known = [(0, empty)] if empty else []
    for mask, weight in entries:
        if mask == 0:
            continue
        check()
        previous = sum(w for t,w in known if t & mask == t)
        if zeta(mask) != previous + weight:
            raise _Reject('incorrect support multiplicity')
        bits = mask
        while bits:
            check()
            bit = bits & -bits
            deleted = mask ^ bit
            previous = sum(w for t,w in known if t & deleted == t)
            if zeta(deleted) != previous:
                raise _Reject('unrecovered proper subsignature')
            bits ^= bit
        known.append((mask,weight))
    if sum(weight for _,weight in entries) != total:
        raise _Reject('missing mass')
    if set(used) != set(proof_table):
        raise _Reject('unused union proof')
    return True
