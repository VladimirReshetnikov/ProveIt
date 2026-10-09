"""Reuse known incidence support to resolve a binary orientation cover.

Order reversal of a pairing is NOT its orientation character. Parity is a
separate supplied bit, justified by geometry outside this module.
"""
from .core import natural, SparseResult


def double_cover_rows(size, signed_rows):
    """signed_rows = (a,b,c,d,order_sign,parity), inclusive endpoints."""
    natural(size, 'size')
    output=[]
    for row in signed_rows:
        if len(row)!=6: raise ValueError('signed pairing needs six entries')
        a,b,c,d,sign,parity=row
        if any(type(x) is not int for x in row):raise ValueError('integer fields required')
        if sign not in (-1,1) or parity not in (0,1):raise ValueError('invalid sign/parity')
        if not (0<=a<=b<size and 0<=c<=d<size and b-a==d-c):
            raise ValueError('invalid signed pairing')
        for sheet in (0,1):
            source=sheet*size;target=(sheet^parity)*size
            output.append((a+source,b+source,c+target,d+target,sign))
    return output


def lift_ports(size, ports):
    from .intervals import prepare_ports
    canonical=prepare_ports(size,ports)
    return tuple(tuple(port)+tuple((a+size,b+size) for a,b in port)
                 for port in canonical)


def refine_double_cover(base: SparseResult, cover_total: int, cover_zeta,
                        *, check=None):
    """Return (signature, consistent_count, inconsistent_count) triples.

    Contract: base is the exact base profile and cover_zeta counts the
    explicitly constructed two-sheeted parity cover with both-sheet marks.
    Since cover support equals base support, only s zeta calls are necessary.
    The returned result is not a proof that the supplied parity is geometric.
    """
    natural(cover_total,'cover total')
    poll=check or (lambda:None)
    done=[];answer=[]
    for t,base_weight in sorted(base.entries,key=lambda item:(item[0].bit_count(),item[0])):
        poll()
        raw=natural(cover_zeta(t),'cover zeta value')
        lifted=raw-sum(w for u,w in done if u & t==u)
        if not base_weight<=lifted<=2*base_weight:
            raise ArithmeticError('cover multiplicity outside binary-cover bounds')
        done.append((t,lifted))
        answer.append((t,lifted-base_weight,2*base_weight-lifted))
    if sum(w for _,w in done)!=cover_total:
        raise ArithmeticError('known-support cover reconstruction did not exhaust total')
    return tuple(answer)
