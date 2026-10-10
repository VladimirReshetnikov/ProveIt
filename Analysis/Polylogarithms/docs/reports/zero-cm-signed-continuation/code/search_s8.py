#!/usr/bin/env python3
"""Independent Euler evaluation and integer-relation search for S8.

The reported residuals are numerical evidence, never proofs of equality.
All finite Euler weights are obtained as exact integers. The analytic tail
bounds are those of the manuscript, signed:thm:euler-certificate and
signed:prop:S-euler. This script uses floating point inside the finite sums.
"""
import json
from math import comb
from pathlib import Path
import time
import mpmath as mp

HERE = Path(__file__).resolve().parents[1]/"results"
BASKET = ['S8', 'g81', 'g63', 'g45', 'g27', 'pi^9',
          'G*zeta(7)', 'beta(4)*zeta(5)', 'beta(6)*zeta(3)', 'beta(8)*log(2)']


def euler_values(N, digits):
    """Stable finite weighted sums; no numerical finite-difference triangle."""
    mp.mp.dps = digits
    pairs = [(8, 1), (6, 3), (4, 5), (2, 7)]
    gvals = [mp.mpf(0) for _ in pairs]
    s8 = mp.mpf(0)
    harmonic = mp.mpf(0)
    harmonics = {b: mp.mpf(0) for a, b in pairs}
    tail = (1 << N) - 1
    c = 1
    denominator = mp.mpf(1 << N)
    for n in range(N):
        if n:
            harmonic += mp.mpf(1) / n
            for b in harmonics:
                harmonics[b] += mp.mpf(1)/(2*n-1)**b + mp.mpf(1)/(2*n)**b
        weight = (-1 if n % 2 else 1) * mp.mpf(tail) / denominator
        s8 += weight * harmonic / (2*n+1)**8
        for j, (a,b) in enumerate(pairs):
            gvals[j] += weight * harmonics[b] / (2*n+1)**a
        c = c * (N-n) // (n+1)
        tail -= c
    assert tail == 0
    return [s8] + gvals


def beta(s):
    return (mp.zeta(s, mp.mpf(1)/4) - mp.zeta(s, mp.mpf(3)/4)) / mp.mpf(4)**s


def basket(N, digits):
    vals = euler_values(N, digits)
    vals += [mp.pi**9, mp.catalan*mp.zeta(7), beta(4)*mp.zeta(5),
             beta(6)*mp.zeta(3), beta(8)*mp.log(2)]
    return vals


def main():
    start = time.time()
    vals = basket(720, 250)
    record = {'basket': BASKET, 'evaluation': {'N':720, 'working_digits':250},
              'values': {k:mp.nstr(v,240) for k,v in zip(BASKET,vals)}}
    print('Evaluation completed in %.3f s' % (time.time()-start), flush=True)
    for dps, tol, maxcoeff, maxsteps in [(150, '1e-140', 10**20, 10000),
                                          (190, '1e-180', 10**25, 20000)]:
        mp.mp.dps = dps
        rel = mp.pslq(mp.matrix(vals), tol=mp.mpf(tol), maxcoeff=maxcoeff,
                     maxsteps=maxsteps)
        print('Search', dps, tol, maxcoeff, ':', rel, flush=True)
        record.setdefault('searches',[]).append({'working_digits':dps,'tol':tol,
                  'maxcoeff':maxcoeff,'maxsteps':maxsteps,'relation':rel})
        if rel and rel[0]:
            record['frozen_relation'] = rel
            record['discovery_residual'] = mp.nstr(mp.fdot(rel,vals), 25)
            break
    if record.get('frozen_relation'):
        highvals = basket(1400, 500)
        record['reevaluation'] = {'N':1400, 'working_digits':500,
           'values':{k:mp.nstr(v,490) for k,v in zip(BASKET,highvals)},
           'integer_residual':mp.nstr(mp.fdot(record['frozen_relation'], highvals),45)}
        print('Independent-length Euler residual',record['reevaluation']['integer_residual'], flush=True)
    record['elapsed_seconds'] = time.time()-start
    (HERE / 's8_search.json').write_text(json.dumps(record,indent=2)+'\n')


if __name__ == '__main__':
    main()
