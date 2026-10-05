"""Fresh scalar derivation from four explicitly stated SL2 generators.

No supplied helper, source program, receipt or saved arithmetic array is read.
This independent check is run before freezing its own source and output.
"""
import hashlib
import json
from pathlib import Path


def inverse(g):
    p, q, s, d = g
    if p*d-q*s != 1:
        raise ValueError('determinant one required')
    return d, -q, -s, p


def upper_conjugate(g):
    p, q, s, d = g
    return p+s, q+d-p-s, s, d-s


def difference_rows(g):
    p, q, s, d = g
    return ((p*p-1, -2*p*q, q*q),
            (-p*s, p*d+q*s-1, -q*d),
            (s*s, -2*s*d, d*d-1))


def first_block(row):
    a, b, c = row
    return [a, b, c, -a+b+c, 0, 0, -2*b-2*c]


def second_block(row):
    a, b, c = row
    return [0, 0, 0, a+b+2*c, b, c, -a-2*b-4*c]


def main():
    generators = [('a', (1, 1, 0, 1)),
                  ('b', (1, 0, 12, 1)),
                  ('z1', (-3, 1, -16, 5)),
                  ('z2', (-7, 1, -64, 9))]
    tables = []
    for name, gen in generators:
        for suffix, g in [('+', gen), ('-', inverse(gen))]:
            left = upper_conjugate(g)
            rows = [first_block(row) for row in difference_rows(left)]
            rows += [second_block(row) for row in difference_rows(g)]
            tables.append({'letter': name+suffix, 'first_SL2': list(left),
                           'second_SL2': list(g), 'coefficients': rows,
                           'nonzero_by_row': [sum(v != 0 for v in row) for row in rows]})
    totals = [sum(t['nonzero_by_row'][i] for t in tables) for i in range(6)]
    result = {'status': 'fresh scalar coefficient derivation', 'tables': tables,
              'row_totals': totals, 'total_nonzero_coefficients': sum(totals),
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'scope': 'Only new scalar formulas from explicit SL2 generators; no stored scientific graph or supplied code read or evaluated.'}
    path = Path('/tmp/positive7_paired_coefficients_fresh_root_check.json')
    if path.exists():
        raise ValueError('refuse to overwrite original output')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'row_totals': totals, 'total': sum(totals),
                      'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}, indent=2))


if __name__ == '__main__':
    main()
