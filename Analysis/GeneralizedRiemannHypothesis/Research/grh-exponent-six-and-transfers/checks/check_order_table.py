#!/usr/bin/env python3
"""Cross-check the two exponent-six lists. Usage: python check_order_table.py author-table.txt fields.csv"""
from ast import literal_eval
from collections import Counter
import csv
from hashlib import sha1
from math import isqrt
from pathlib import Path
import sys


def require(check, message):
    if not check:
        raise ValueError(message)


def field_discriminant(d):
    """The fundamental discriminant in the square class of negative d."""
    radical, n, p = -1, -d, 2
    while p*p <= n:
        odd_power = False
        while n % p == 0:
            n //= p
            odd_power = not odd_power
        if odd_power:
            radical *= p
        p += 1
    radical *= n
    return radical if radical % 4 == 1 else 4*radical


def main(order_path, field_path):
    data = Path(order_path).read_bytes()
    blob = sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    require(blob == 'fc8d109c749eb73efab6bc5d9f058c5c78cd8c8f', 'unexpected author table')
    lines = data.decode().splitlines()
    orders = literal_eval(lines[2])
    require(len(orders) == len(set(orders)) == 1236, 'order count or duplicate')
    groups = []
    for line in lines:
        if line.startswith("Group="):
            _, subgroup = line.split(': ', 1)
            groups.extend(literal_eval(subgroup))
    require(sorted(groups) == sorted(orders), 'group breakdown')
    maximal = set()
    conductor_counts = Counter()
    for d in orders:
        d0 = field_discriminant(d)
        f = isqrt(d//d0)
        require(d0*f*f == d, 'invalid order discriminant')
        conductor_counts[f] += 1
        if f == 1:
            maximal.add(d)
    with open(field_path, newline='') as src:
        fields = {int(r['fundamental_discriminant']) for r in csv.DictReader(src)}
    require(maximal == fields and len(maximal) == 432, 'field list mismatch')
    require(min(orders) == -43522752, 'largest absolute order discriminant')
    print('1236 distinct order discriminants; maximum absolute discriminant 43522752.')
    print('432 are maximal, identical to the field census. The other 804 are nonmaximal.')
    print('Counts by conductor:', sorted(conductor_counts.items()))


if __name__ == '__main__':
    main(*sys.argv[1:])
