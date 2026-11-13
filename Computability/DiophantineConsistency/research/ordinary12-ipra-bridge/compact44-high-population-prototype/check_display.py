#!/usr/bin/env python3
"""External high-list transcription check; not a Lean graph-port theorem."""
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[2]
COEFFICIENTS = BASE / 'candidates/ten-positive-shifted-strong/coefficients'
PINS = {
    HERE / 'CompactHighPopulation.lean': 'b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d',
    COEFFICIENTS / 'MF_source.bin.gz': '935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c6e3b',
    COEFFICIENTS / 'beta.bin.gz': '466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c',
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(b):
    return hashlib.sha256(b).hexdigest()


def main():
    data = {p: p.read_bytes() for p in PINS}
    for p, expected in PINS.items():
        require(digest(data[p]) == expected, 'input pin ' + str(p))
    source = data[HERE / 'CompactHighPopulation.lean'].decode()
    definition = '''def highDigits : List ℕ :=
  [4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++
  List.replicate 42 0 ++ List.replicate 9 1 ++
  List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++
  List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++
  List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]'''
    require(source.count(definition) == 1 and source.count('def highDigits :') == 1,
            'exact list source form')
    require(all(source.count(x) == 1 for x in (
        'def mu : ℕ := 2^51-2', 'def padding : ℕ := 2^65-1',
        'def lastPadding : ℕ := 2^19-1')), 'digit source definitions')
    mu, padding, last = (1 << 51) - 2, (1 << 65) - 1, (1 << 19) - 1
    digits = ([4] + [0] * 1012 + [1] * 10 + [0] * 42 + [1] * 9 +
              [0] * 1121 + [1] + [0] * 1100 + [1] + [0] * 1096 +
              [mu] + [0] * 1101 + [mu] + [0] * 3296 + [padding] * 13 + [last, 0])
    rho = 1 << 67
    require(len(digits) == 8807 and all(0 <= x < rho for x in digits), 'digit bounds')
    require(sum(x.bit_count() for x in digits) == 986, 'population')
    beta = int.from_bytes(gzip.decompress(data[COEFFICIENTS / 'beta.bin.gz']), 'little')
    shifted = int.from_bytes(gzip.decompress(data[COEFFICIENTS / 'MF_source.bin.gz']), 'little')
    require(beta == (1 << 590069) - 1 and shifted >= beta, 'beta/split')
    high = shifted - beta
    def matches(candidate):
        return (sum(d << (67 * i) for i, d in enumerate(candidate) if d) == high and
                all(((high >> (67 * i)) & (rho - 1)) == d
                    for i, d in enumerate(candidate)))
    require(matches(digits), 'native high value or individual digit')
    for name, index in [('origin', 0), ('clause', 4393), ('padding', 8805)]:
        altered = digits.copy()
        altered[index] ^= 1
        require(not matches(altered), 'mutation survived ' + name)
    for p, expected in PINS.items():
        require(digest(p.read_bytes()) == expected, 'post-check input drift ' + str(p))
    print(json.dumps({'status': 'PASS_COMPACT_HIGH_LIST_EXTERNAL', 'length': len(digits),
                      'population': 986, 'digits_checked': len(digits),
                      'mutations_rejected': ['origin', 'clause', 'padding']}))


if __name__ == '__main__':
    main()
