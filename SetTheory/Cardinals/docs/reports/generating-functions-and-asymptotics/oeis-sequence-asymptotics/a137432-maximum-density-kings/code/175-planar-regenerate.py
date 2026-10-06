#!/usr/bin/env python3
"""Optional exact certificate regeneration; requires installed SymPy (tested 1.14).

No recurrence fitting is used. Rebuild physical T; use its Boolean block
triangularity to obtain det(I-zT) as the product of diagonal determinants.
The adjugate numerator has fewer than N coefficients even when the determinant
has smaller degree due to zero eigenvalues. Preserve all those N slots before
cancelling. The independent standard-library verifier checks the resulting GF.
This script downloads nothing and never installs a dependency.
"""
from __future__ import annotations
import argparse
from itertools import product
import json
from pathlib import Path
import sys
import sympy as sp
import verify as v

z = sp.Symbol('z')


def polynomial(a):
    return sp.Poly.from_list(list(reversed(a)), gens=z)


def integer_coefficients(p):
    p = sp.Poly(p, z)
    values = [p.nth(i) for i in range(int(p.degree())+1)]
    v.require(all(value.is_Integer for value in values), 'regenerated noninteger coefficient')
    return [int(value) for value in values]


def factors(a):
    _, factorization = sp.factor_list(polynomial(a))
    result = []
    for f, exponent in factorization:
        f = sp.Poly(f, z)
        normalized = f.as_expr()/f.nth(0)
        result.append({'coefficients': integer_coefficients(normalized), 'exponent': int(exponent)})
    # Stable order by degree and then the complete constant-one coefficient tuple.
    return sorted(result, key=lambda entry: (len(entry['coefficients']), entry['coefficients']))


def generate_height(h):
    keys, successors = v.build_transfer(h)
    n = len(keys)
    index = {key: i for i, key in enumerate(keys)}
    full_denominator, blocks = [1], []
    for word in product((0, 1), repeat=h):
        indices = [index[word, u] for u in range(h+1)]
        block = [[int(j in successors[i]) for j in indices] for i in indices]
        determinant = v.gram_block(word, block)
        full_denominator = v.mul(full_denominator, determinant)
        blocks.append({'word': ''.join(map(str, word)), 'determinant': determinant,
                       'factors': factors(determinant)})
    seq = v.sequence(successors, max(n, 6))
    # Full adjugate numerator, with all N slots retained before reduction.
    s_numerator = v.trim([sum(full_denominator[j]*seq[k-j]
                             for j in range(min(k, len(full_denominator)-1)+1))
                          for k in range(n)])
    raw_p, raw_q = polynomial([0]+s_numerator), polynomial(full_denominator)
    common = sp.gcd(raw_p, raw_q)
    p, p_rem = sp.div(raw_p, common)
    q, q_rem = sp.div(raw_q, common)
    v.require(p_rem.is_zero and q_rem.is_zero, 'exact cancellation failed')
    normalizer = q.nth(0)
    p = integer_coefficients(p.as_expr()/normalizer)
    q = integer_coefficients(q.as_expr()/normalizer)
    factored = factors(q)
    maxima = {}
    for entry in factored:
        degree = str(len(entry['coefficients'])-1)
        maxima[degree] = max(maxima.get(degree, 0), entry['exponent'])
    alpha, beta = v.dominant_coefficients(h, p, q)
    result = {'h': h, 'states': n, 'allowed_pairs': sum(map(len, successors)),
              'counts_w_1_to_6': seq[:6], 'recurrence_onset': max(len(p)-1, len(q)-1),
              'numerator': p, 'denominator': q, 'factors': factored,
              'maximum_exponents_by_degree': maxima, 'gram_blocks': blocks,
              'alpha': str(alpha), 'beta': str(beta)}
    # Regeneration is not a replacement for the separate certificate verifier.
    v.verify_height(result)
    return result


def metadata():
    return {
        'schema_version': 1,
        'convention': 'F_h(z)=sum_{w>=1} P_h(w) z^w; ascending polynomial coefficients; Q_h(0)=1',
        'producer': 'Original Report175 exact-code implementation, prepared 2026-10-03 with OpenAI assistance',
        'regeneration_method': 'Physical-state transfer; product of full diagonal characteristic determinants; N-slot adjugate numerator; exact polynomial cancellation; no fitted recurrence',
        'verification_method': 'Independent physical-row all-cardinality DP; N consecutive Cayley-Hamilton residuals; exact primitive polynomial gcd and low-degree irreducibility tests',
        'sources': [
            {'author': 'Herbert S. Wilf', 'title': 'The Problem of the Kings', 'year': 1995, 'url': 'https://doi.org/10.37236/1197'},
            {'author': 'Donald E. Knuth', 'title': 'Non-attacking Kings on a Chessboard', 'year': 1994, 'url': 'https://www-cs-faculty.stanford.edu/~knuth/papers/nkc.tex'},
            {'author': 'Vaclav Kotesovec', 'title': 'Non-attacking Chess Pieces, sixth edition', 'year': 2013, 'pages': '82-90, especially 83', 'url': 'http://www.kotesovec.cz/books/kotesovec_non_attacking_chess_pieces_2013_6ed.pdf'},
            {'author': 'Tricia Muldoon Brown', 'title': 'Maximum arrangements of nonattacking kings on the 2n x 2n chessboard', 'year': 2025, 'url': 'https://doi.org/10.2478/rmm-2025-0003'},
        ]
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--extended', action='store_true', help='explicitly regenerate through h=6')
    parser.add_argument('--max-h', type=int, choices=range(1, 7))
    parser.add_argument('--output', type=Path, help='write regenerated JSON here; no write by default')
    parser.add_argument('--compare', type=Path, help='compare all generated heights exactly with this certificate file')
    args = parser.parse_args()
    maximum = args.max_h if args.max_h is not None else (6 if args.extended else 4)
    if maximum > 4 and not args.extended:
        parser.error('heights 5 and 6 require explicit --extended')
    if args.output and (args.output.exists() or args.output.is_symlink()):
        parser.error('output already exists; choose a new file')
    reference = None
    if args.compare:
        reference = json.loads(args.compare.read_text(encoding='utf-8'))['heights']
        v.require(len(reference) >= maximum, 'comparison file lacks requested heights')
    result = metadata()
    result['heights'] = []
    for h in range(1, maximum+1):
        entry = generate_height(h)
        if reference is not None:
            v.require(entry == reference[h-1], f'h={h}: regeneration differs from certificate')
        result['heights'].append(entry)
        print(f'h={h}: regenerated and independently verified; deg Q={len(entry["denominator"])-1}', flush=True)
    if args.output:
        with args.output.open('x', encoding='utf-8') as stream:
            stream.write(json.dumps(result, indent=2, ensure_ascii=True)+'\n')
        print(f'Wrote {args.output}')
    print('REGENERATION PASSED' + ('; certificate comparison exact' if reference is not None else ''))


if __name__ == '__main__':
    try:
        main()
    except (v.VerificationError, ValueError, KeyError, TypeError, OSError) as exc:
        print(f'REGENERATION FAILED: {exc}', file=sys.stderr)
        sys.exit(1)
