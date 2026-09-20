#!/usr/bin/env python3
"""Exact checks for the binary defect and universal denominator theorems.

Only the Python standard library is required. The proof is in article.tex;
these finite tests detect arithmetic and transcription errors, not prove it.
"""
from __future__ import annotations

import json
import time
from fractions import Fraction
from math import gcd
from pathlib import Path

from verify import (diagonal, divisors, generalized_binomial, mobius, require,
                    valuation, write_csv)


def run(outdir: Path) -> dict:
    started = time.perf_counter()
    data = outdir / 'data'
    data.mkdir(parents=True, exist_ok=True)
    counts: dict[str, int] = {}
    rows = []
    for alpha in range(-5, 6):
        for beta in range(-5, 6):
            for m in range(1, 16, 2):
                for r in range(2, 8):
                    n = m * 2**r
                    if n > 2000:
                        continue
                    defect = diagonal(n, alpha, beta) - diagonal(n//2, alpha, beta)
                    e = 3*r-3
                    bit = (alpha*beta*generalized_binomial(
                        (alpha+beta+1)*m-1, m-1)) % 2
                    require((defect-2**e*bit) % 2**(e+1) == 0,
                            f'binary defect formula failed: {(alpha,beta,m,r)}')
                    v = valuation(defect, 2)
                    rows.append(dict(alpha=alpha, beta=beta, m=m, r=r, n=n,
                                     base_exponent=e, predicted_bit=bit,
                                     actual_valuation='infinity' if v is None else v))
    counts['binary_leading_defect_checks'] = len(rows)
    write_csv(data/'binary_defect_checks.csv', list(rows[0]), rows)

    first = 0
    for alpha in range(-5, 6):
        for beta in range(-5, 6):
            for m in range(1, 32, 2):
                require((diagonal(2*m,alpha,beta)-diagonal(m,alpha,beta)) % 2 == 0,
                        f'first binary layer failed: {(alpha,beta,m)}')
                first += 1
    counts['binary_first_layer_checks'] = first

    # Stronger than the proof needs: H_(2j)/j^2 is an odd local integer.
    h = Fraction(0)
    for j in range(1, 401):
        h += Fraction(1, 2*j-1)
        k = h / j**2
        require(k.numerator % 2 == 1 and k.denominator % 2 == 1,
                f'odd harmonic normalization failed at {j}')
    counts['exact_harmonic_unit_checks'] = 400

    denominator_rows = []
    for n in range(1, 1001):
        raw = sum(mobius(d)*diagonal(n//d) for d in divisors(n))
        b = Fraction(raw, n**3)
        p, rem = divmod(raw, n)
        require(rem == 0 and p >= 0, f'primitive orbit integrality failed: {n}')
        require(12 % b.denominator == 0,
                f'denominator-12 theorem failed: {n}')
        divisor = n*n//gcd(n*n,12)
        require(p % divisor == 0, f'primitive orbit divisibility failed: {n}')
        denominator_rows.append(dict(n=n, primitive_orbits=p,
                                      B_n=str(b), twelve_B_n=12*b.numerator//b.denominator,
                                      proved_divisor=divisor))
    counts['target_denominator_and_orbit_checks'] = len(denominator_rows)
    write_csv(data/'denominator12.csv', list(denominator_rows[0]), denominator_rows)

    gen_count = 0
    for alpha in range(-3,4):
        for beta in range(-3,4):
            common_denominator = 12 if alpha*beta % 2 == 0 else 24
            for n in range(1,101):
                raw = sum(mobius(d)*diagonal(n//d,alpha,beta) for d in divisors(n))
                require((common_denominator*raw) % n**3 == 0,
                        f'general denominator theorem failed: {(alpha,beta,n)}')
                gen_count += 1
    counts['general_denominator_checks'] = gen_count

    # Exact infinite-family sharpness theorem, sampled at finite levels.
    sharp_count = 0
    for alpha in [-5,-3,-1,1,3,5]:
        for beta in [-5,-3,-1,1,3,5]:
            for r in range(2,10):
                defect = diagonal(2**r,alpha,beta)-diagonal(2**(r-1),alpha,beta)
                require(valuation(defect,2) == 3*r-3,
                        f'odd-parameter sharpness failed: {(alpha,beta,r)}')
                sharp_count += 1
    require(Fraction(diagonal(4)-diagonal(2), 4**3) == Fraction(5,4), 'B4')
    require(Fraction(diagonal(3)-diagonal(1), 3**3) == Fraction(2,3), 'B3')
    counts['binary_sharpness_checks'] = sharp_count + 2

    # This last table is explicitly exploratory. No assertion in the proof
    # depends on the conjectural exact valuation 3r+1 for the basket sequence.
    exploratory = []
    for m in range(1,16,2):
        for r in range(1,10):
            n = m*2**r
            defect = diagonal(n)-diagonal(n//2)
            exploratory.append(dict(m=m,r=r,n=n,valuation=valuation(defect,2),
                                    proved_exponent=(1 if r==1 else 3*r-2)))
    for r in range(10,16):
        n = 2**r
        defect = diagonal(n)-diagonal(n//2)
        exploratory.append(dict(m=1,r=r,n=n,valuation=valuation(defect,2),
                                proved_exponent=3*r-2))
    counts['exploratory_binary_values_not_proof'] = len(exploratory)
    write_csv(data/'binary_valuations.csv', list(exploratory[0]), exploratory)

    report = dict(status='PASS', counts=counts,
                  elapsed_seconds=round(time.perf_counter()-started,3),
                  note='Finite exact tests; theorems are established by the article proofs. '
                       'The exploratory valuation table is not a proved general formula.')
    (outdir/'binary_report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    text = 'Binary and denominator checks: PASS\n\n'
    text += '\n'.join(f'{k}: {v}' for k,v in counts.items())
    text += '\n\n'+report['note']+'\n'
    (outdir/'binary_report.txt').write_text(text,encoding='utf-8')
    print(text)
    return report


if __name__ == '__main__':
    run(Path(__file__).resolve().parent)
