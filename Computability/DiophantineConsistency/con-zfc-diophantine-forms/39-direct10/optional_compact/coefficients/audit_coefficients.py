#!/usr/bin/env python3
"""Independent reader for the bounded-checksum coefficient tuple.

No builder functions are imported. The four full integers are reconstructed
using the literal tile table and directly written formulas.
"""
from pathlib import Path
from hashlib import sha256
from math import isqrt
import gzip
import json

ROOT = Path(__file__).resolve().parent


def check(condition, label):
    if not condition:
        raise ValueError(label)


def main():
    manifest = json.loads((ROOT / 'COEFFICIENT_BINDING.json').read_text())
    decoded = {}
    for record in manifest['materialization']['files']:
        compressed = (ROOT / record['file']).read_bytes()
        check(sha256(compressed).hexdigest() == record['gzip_sha256'], 'gzip hash')
        raw = gzip.decompress(compressed)
        check(sha256(raw).hexdigest() == record['sha256'], 'raw hash')
        decoded[record['port']] = int.from_bytes(raw, 'little')
        check(len(raw) == record['raw_bytes'], 'raw length')
        check(decoded[record['port']].bit_length() == record['bits'], 'bit length')

    b, length, d = 67, 8807, 590069
    radix = 2**b
    base = decoded['beta'] + 1
    check(base == 2**d and d == b * length, 'base')
    spatial, current = divmod(decoded['K'], base)
    check(spatial == 2**(67 * 42), 'spatial multiplier')
    high = decoded['MF_source'] - decoded['beta']
    check(0 < high < base-1 and 0 < decoded['MC'] < base-1, 'mask bounds')
    check(high % 8 == 4 and decoded['MC'] % 4 == 2, 'low residues')
    check(high.bit_count() == 986 and decoded['MC'].bit_count() == d-986,
          'population balance')

    tile_bytes = (ROOT / 'wang943_tiles.json').read_bytes()
    check(sha256(tile_bytes).hexdigest() ==
          '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
          'literal tile hash')
    tiles = json.loads(tile_bytes)
    words = []
    coefficients = {}
    for index, (west, north, east, south) in enumerate(tiles):
        # Direct concatenation, independently of the builder's generic slots.
        labels = west + north*2**8 + east*2**17 + south*2**25
        word = labels + 127*2**34
        words.append(word)
        coefficients[index] = 1 + (2**34-labels)*1024
        check(0 < word < 2**41 and 0 < 2**41-word < 2**41, 'word bounds')
    for slot, (offset, count, position) in enumerate(((1023,9,0),(1013,10,8),(1003,9,17),(983,10,25))):
        for j in range(count-1):
            coefficients[offset+j] = 2**(10+position+j)
        coefficients[offset+count-1] = 2**(44+slot)
    for e, bit in ((1095,38),(2195,39),(3296,40)):
        coefficients[e] = 2**(10+bit)
    coefficients[1063] = coefficients[1064] = 0
    support = set(coefficients)
    check(len(support) == 986, 'support size')
    mask = 1022 + 1024*(2**41-1)
    expected_current = sum(2**(b*e) for e in (30,62,1100,2201))
    for e, c in coefficients.items():
        expected_current += c*(2**(b*(4393-e)) + 2**(b*(5495-e)))
    check(current == expected_current, 'full current coefficient')
    expected_low = base-1-sum(2**(b*e) for e in support-{1})-2*2**(b*1063)
    check(decoded['MC'] == expected_low, 'full low mask')
    targets = list(range(1013,1023)) + list(range(1065,1074)) + [2195,3296]
    expected_high = 4 + mask*(2**(b*4393)+2**(b*5495))
    expected_high += sum(2**(b*e) for e in targets)
    expected_high += (2**65-1)*sum(2**(b*e) for e in range(8792,8805))
    expected_high += (2**19-1)*2**(b*8805)
    check(high == expected_high, 'full high mask')

    digits = {}
    value, e = current, 0
    while value:
        value, digit = divmod(value, radix)
        if digit:
            digits[e] = digit
        e += 1
    expected = [(1013+j,983+j,None,1013+j) for j in range(10)]
    expected += [(1065+j,1003+j,1023+j,None) for j in range(9)]
    expected += [(2195,1095,None,2195),(3296,1095,None,3296)]
    native_checks = 0
    for target, cur, space, temporal in expected:
        for e in support:
            check(digits.get(target-e,0) == (e == cur), 'current native identity')
            check((e+42 == target) == (e == space), 'spatial native identity')
            check((e == target) == (e == temporal), 'temporal native identity')
            native_checks += 3
    for target in (4393,5495):
        for e in support:
            check(digits.get(target-e,0) == coefficients[e], 'clause identity')
            check(e+42 != target, 'spatial clause separation')
            native_checks += 2
    check({(4393-e)%length for e in support}.isdisjoint(
          {(5495-e)%length for e in support}), 'clean band separation')
    check({(2195-e)%length for e in support} & {(3296-e)%length for e in support}
          == {0}, 'anchor synchronization')
    mass = 988*(2*sum(coefficients.values())+6)
    check(max(4*mass+8, 2*mask+4, 2*(2**65-1)+4, 16) < radix, 'carry bound')
    check(max(digits)+max(support) == 8791 and 8805 < length, 'padding separation')

    check([n for n in range(944) if n & 1022 == 0] == [0,1], 'selector extraction')
    mutation_count = 0
    for i, word in enumerate(words):
        check((coefficients[i]+1024*word) & mask == 0, 'true clause')
        for bit in range(41):
            wrong = word ^ (1 << bit)
            check((coefficients[i]+1024*wrong) & mask != 0, 'one-bit mutation rejection')
            mutation_count += 1
    # For each actual word, the open interval contains exactly one nonzero
    # multiple of 2^41. These finite endpoint checks support the general proof.
    check(all(0 < 2**41-u and 2**41-u+(2**41-1) < 2**42 for u in words),
          'strict universal decoding intervals')

    prime, step = 581197, 581196
    check(d == 67*8807 and step % 290598 == 0, 'd and controller period')
    for p in (67,8807,prime):
        check(all(p % k for k in range(2,isqrt(p)+1)), 'primality')
    orders = [(67,66,[2,3,11]),(8807,4403,[7,17,37]),(prime,581196,[2,3,7,11,17,37])]
    for p, order, prime_factors in orders:
        check(pow(base,order,p) == 1, 'order upper bound')
        check(all(pow(base,order//q,p) != 1 for q in prime_factors), 'order exactness')
        check(step % order == 0, 'common controller step')
    lift = pow(base,step,prime*prime)
    check(lift == 182964883980 and lift % prime == 1 and lift != 1, 'valuation one')
    unit_rows = []
    for p in (67,8807,prime):
        bp = base % p
        first = (bp*bp-1) % p
        second = (1+bp*(current%p)+bp*bp*(spatial%p+1)) % p
        check(first and second, 'actual rank multiplier unit')
        unit_rows.append({'prime':p,'B_squared_minus_one':first,'H0':second})
    result = dict(status='PASS',full_integer_reconstructions=4,
                  native_basis_identities=native_checks,
                  canonical_tile_clauses_checked=943,
                  one_bit_negative_controls=mutation_count,
                  actual_coefficient_unit_checks=unit_rows,
                  total_raw_bytes=sum(r['raw_bytes'] for r in manifest['materialization']['files']),
                  scope='Finite exact interface audits; see PROOF.md for unbounded arguments.')
    (ROOT / 'INDEPENDENT_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
