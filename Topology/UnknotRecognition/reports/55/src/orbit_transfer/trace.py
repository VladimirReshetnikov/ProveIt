"""Native-schema AHT local proof replay; no orbit-search producer is imported.

Adapted from ProveIt's MIT-0 interval_orbit_verify.py, blob
0ccb56a0e8b5f1255384121d7417441314727720. This is an independently
packaged adaptation, not a byte-identical upstream copy.
Inclusive pairings; emitted transport operations use half-open intervals.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import gcd
import re
from typing import Callable, Iterable


class InvalidTrace(ValueError):
    pass


def integer(value: object) -> int:
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r'[+-]?0[xX][0-9a-fA-F]+', value):
        return int(value, 16)
    raise InvalidTrace('expected an integer or hexadecimal string, not a boolean')


def normalize(raw: object, size: int) -> tuple[int, int, int, int, int]:
    if isinstance(raw, (list, tuple)) and len(raw) == 5:
        a, b, c, d, sign = map(integer, raw)
    elif all(hasattr(raw, name) for name in ('a', 'b', 'c', 'd', 'reverse')):
        if type(raw.reverse) is not bool:
            raise InvalidTrace('reverse must be boolean')
        a, b, c, d = (integer(getattr(raw, name)) for name in ('a', 'b', 'c', 'd'))
        sign = -1 if raw.reverse else 1
    else:
        raise InvalidTrace('expected an inclusive pairing row or native pairing')
    if sign not in (-1, 1) or not (0 <= a <= b < size and 0 <= c <= d < size):
        raise InvalidTrace('invalid pairing endpoints or sign')
    if b-a != d-c:
        raise InvalidTrace('unequal pairing widths')
    return (a, b, c, d, sign) if a <= c else (c, d, a, b, sign)


def gaps_of(size: int, rows: list[tuple]) -> list[tuple[int, int]]:
    result, end = [], 0
    for lo, hi in sorted((lo, hi) for a,b,c,d,_ in rows for lo,hi in ((a,b),(c,d))):
        if lo > end:
            result.append((end, lo))
        end = max(end, hi+1)
    if end < size:
        result.append((end, size))
    return result


def shifted_rows(rows: list[tuple], gaps: list[tuple]) -> list[tuple]:
    def shift(x):
        return x-sum(hi-lo for lo,hi in gaps if hi <= x)
    return [tuple(shift(x) for x in row[:4])+(row[4],) for row in rows]


def transmitted(carrier: tuple, target: tuple, sp: int, tp: int, size: int) -> tuple:
    def inverse(lo, hi, power):
        if power < 0:
            raise InvalidTrace('negative inverse power')
        if power == 0:
            return 1, 0
        a,b,c,d,s = carrier
        if not c <= lo <= hi <= d:
            raise InvalidTrace('undefined partial inverse')
        if s == -1:
            if power != 1 or b >= c:
                raise InvalidTrace('reflection inverse requires a trimmed carrier')
            return -1, a+d
        p = c-a
        if p <= 0 or lo-(power-1)*p < c:
            raise InvalidTrace('translation power exceeds its partial domain')
        return 1, -power*p
    if tp < 1:
        raise InvalidTrace('target range must move')
    a,b,c,d,s = target
    e,u = inverse(a,b,sp)
    f,v = inverse(c,d,tp)
    return normalize([*sorted((e*a+u,e*b+u)), *sorted((f*c+v,f*d+v)), e*s*f],size)


@dataclass(frozen=True)
class Transport:
    kind: str
    old_size: int
    new_size: int
    parameter: int = 0
    gaps: tuple[tuple[int,int], ...] = ()


@dataclass(frozen=True)
class CheckedTrace:
    size: int
    orbit_count: int
    operations: tuple[Transport,...]
    source_events: int


def check_trace(size: int, pairings: Iterable, proof: dict,
                check: Callable[[],None] | None = None) -> CheckedTrace:
    """Check all local rules and return only the certified weight-moving events.

    Source binding includes pairing order. This verifies supplied relations,
    never their interpretation as a knot exterior. Callback exceptions propagate.
    """
    poll = check if check is not None else lambda: None
    poll()
    original = size = integer(size)
    if size < 0 or not isinstance(proof,dict):
        raise InvalidTrace('invalid source')
    if integer(proof.get('size')) != size:
        raise InvalidTrace('source size differs')
    version = integer(proof.get('version'))
    if version not in (1,2):
        raise InvalidTrace('unsupported proof version')
    rows = [normalize(row,size) for row in pairings]
    raw = proof.get('pairings')
    if not isinstance(raw,list) or any(not isinstance(row,(list,tuple)) for row in raw):
        raise InvalidTrace('missing pairing binding')
    supplied = [normalize(row,size) for row in raw]
    if rows != supplied or [tuple(map(integer,row)) for row in raw] != supplied:
        raise InvalidTrace('pairing binding is noncanonical or different')
    claimed = integer(proof.get('orbit_count'))
    if not 0 <= claimed <= size:
        raise InvalidTrace('impossible orbit count')
    events = proof.get('operations')
    if not isinstance(events,list):
        raise InvalidTrace('missing operations')
    count, transport = 0, []
    def index(x):
        x = integer(x)
        if not 0 <= x < len(rows):
            raise InvalidTrace('pairing index out of range')
        return x
    for event in events:
        poll()
        if not isinstance(event,dict):
            raise InvalidTrace('invalid event')
        op = event.get('op')
        if op == 'delete':
            i = index(event.get('index')); a,b,c,d,s = rows[i]
            if a != c or (s != 1 and a != b):
                raise InvalidTrace('only identities may be deleted')
            rows.pop(i)
        elif op == 'trim':
            i = index(event.get('index')); a,b,c,d,s = rows[i]
            if s != -1 or b < c or a == d:
                raise InvalidTrace('not a trimmable reflection')
            end = (a+d-1)//2
            rows[i] = normalize((a,end,a+d-end,d,-1),size)
        elif op == 'merge':
            i,j = index(event.get('left')),index(event.get('right'))
            if i == j:
                raise InvalidTrace('identical merger operands')
            a,b,c,d,s = rows[i]; aa,bb,cc,dd,ss = rows[j]
            p,q = c-a,cc-aa
            if not (s == ss == 1 and 0 < p <= b-a+1 and 0 < q <= bb-aa+1):
                raise InvalidTrace('nonperiodic merger')
            g = gcd(p,q)
            if min(d,dd)-max(a,aa)+1 < p+q-(g if version == 2 else 0):
                raise InvalidTrace('insufficient periodic overlap')
            lo,hi = min(a,aa),max(d,dd)
            i,j = sorted((i,j)); rows[i] = (lo,hi-g,lo+g,hi,1); rows.pop(j)
        elif op == 'transmit':
            i,j = index(event.get('transmitter')),index(event.get('target'))
            if i == j:
                raise InvalidTrace('self transmission')
            rows[j] = transmitted(rows[i],rows[j],integer(event.get('source_power')),
                                  integer(event.get('target_power')),size)
        elif op == 'contract':
            expected = gaps_of(size,rows)
            actual = event.get('gaps')
            if not expected or not isinstance(actual,list):
                raise InvalidTrace('invalid static gaps')
            if any(not isinstance(g,(list,tuple)) or len(g) != 2 for g in actual):
                raise InvalidTrace('malformed gap')
            decoded = [(integer(g[0]),integer(g[1])+1) for g in actual]
            if decoded != expected:
                raise InvalidTrace('gaps differ from static complement')
            removed = sum(hi-lo for lo,hi in expected)
            transport.append(Transport('contract',size,size-removed,gaps=tuple(expected)))
            rows = shifted_rows(rows,expected); size -= removed; count += removed
        elif op == 'truncate':
            i = index(event.get('index')); cut = integer(event.get('new_size'))
            a,b,c,d,s = rows[i]
            if not (0 <= cut < size and d == size-1 and c <= cut):
                raise InvalidTrace('invalid truncation suffix')
            if (s == 1 and c <= a) or (s == -1 and b >= c):
                raise InvalidTrace('invalid truncation carrier')
            for j,(_,bb,_,dd,_) in enumerate(rows):
                if j != i and (bb >= cut or dd >= cut):
                    raise InvalidTrace('another pairing meets removed suffix')
            transport.append(Transport('translation' if s == 1 else 'reflection',
                                       size,cut,c-a if s == 1 else a))
            if cut == c:
                rows.pop(i)
            else:
                lost = size-cut
                row = (a,b-lost,c,cut-1,1) if s == 1 else (a+lost,b,c,cut-1,-1)
                rows[i] = normalize(row,cut)
            size = cut
        else:
            raise InvalidTrace('unknown operation')
    if size or rows or count != claimed:
        raise InvalidTrace('unfinished trace or incorrect final count')
    return CheckedTrace(original,count,tuple(transport),len(events))
