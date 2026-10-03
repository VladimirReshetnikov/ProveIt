#!/usr/bin/env python3
"""Exact rational checks of the strictness formulas, not a substitute for proof."""
from fractions import Fraction as F
from pathlib import Path
import json

# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result beside itself, with CRLF on Windows). Pass
# --output-dir with this program's own directory, on a copy, to regenerate
# the recorded file.
def _ed_write(name, text):
    import argparse
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))


def phi(h, u, v):
    return max(0, min(h, u, v, u + v - h))


def positive_affine_mean(left, right):
    if left >= 0 and right >= 0:
        return (left + right) / 2
    if left <= 0 and right <= 0:
        return F(0)
    if left > 0:
        return left * left / (2 * (left - right))
    return right * right / (2 * (right - left))


def chord_integral(g, shift):
    G = [F(0)]
    for v in g:
        G.append(G[-1] + v)
    return sum((positive_affine_mean(G[i + shift] - G[i],
                                     G[i + shift + 1] - G[i + 1])
                for i in range(len(g) - shift)), F(0))


def main():
    level_count = affine_count = 0
    for a in range(2, 13):
        for b in range(1, a):
            L = a + b
            for ui in range(1, 4 * L):
                for vi in range(1, 4 * L - ui + 1):
                    u, v = F(ui, 4), F(vi, 4)
                    gap = phi(b, u, v) - phi(a, u, v)
                    criterion = u < a and v < a and b < u + v < L
                    assert gap >= 0 and (gap > 0) == criterion
                    level_count += 1
            for sign in (-1, 1):
                for numerator in (1, 2, 3):
                    kappa = F(sign * numerator, 2 * L)
                    assert 1 - abs(kappa) * L / 2 > 0
                    # h(s)=1+kappa(s-L/2) is positive, affine, log-concave and mean one.
                    tv_a = positive_affine_mean(-kappa * a / 2, kappa * a / 2)
                    tv_b = positive_affine_mean(-kappa * b / 2, kappa * b / 2)
                    assert tv_a - tv_b == abs(kappa) * (a - b) / 8 > 0
                    affine_count += 1
    g = tuple(map(F, (-1, 0, 0, 0, 1)))
    G = [F(0)]
    for value in g:
        G.append(G[-1] + value)
    signed = sum(((G[i + 2] - G[i] + G[i + 3] - G[i + 1]) / 2
                  for i in range(3)), F(0))
    assert signed == 0
    assert chord_integral(g, 2) == chord_integral(g, 3) == F(1, 2)
    result = dict(status='passed', arithmetic='exact rational',
                  strict_level_comparisons=level_count, normalized_affine_profiles=affine_count,
                  generic_counterexample={'a':3,'b':2,'cell_values':[-1,0,0,0,1],
                                          'signed_rectangle_integral':'0','J_a':'1/2','J_b':'1/2'},
                  scope='Finite regression checks; the manuscript proves every stated parameter case.')
    # ed. (2026-10-01): written by _ed_write (see above).
    _ed_write('strictness_exact.json', json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
