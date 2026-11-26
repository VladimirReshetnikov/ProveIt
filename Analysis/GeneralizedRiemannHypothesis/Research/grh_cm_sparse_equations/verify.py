#!/usr/bin/env python3
"""Replay the CM classifications and the bounded-width obstruction, offline."""
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
from fractions import Fraction

ROOT = Path(__file__).resolve().parent
CERT = ROOT / 'certificates'
PRIOR = ROOT / 'prior'
RECORDED = ROOT / 'verification'

def run(args, output=None, error_output=None, settings=None):
    """Run with assertions enabled and stop at the first failed calculation."""
    env = os.environ.copy()
    env.pop('PYTHONOPTIMIZE', None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    from contextlib import ExitStack
    if settings:
        env.update(settings)
    with ExitStack() as streams:
        out = streams.enter_context(output.open('wb')) if output is not None else None
        err = streams.enter_context(error_output.open('wb')) if error_output is not None else None
        subprocess.run([str(x) for x in args], check=True, stdout=out, stderr=err, env=env)

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def same(a, b):
    require(a.read_text().splitlines() == b.read_text().splitlines(), f'Mismatch between {a} and {b}')

def compile_program(source, target):
    run([os.environ.get('CXX', 'c++'), '-std=c++17', '-O3', source, '-o', target])

def separate(D, a, b):
    return D >= 16*a*a and 9*D*(b-a)**2 >= 16*a*a*b*b

def main():
    with tempfile.TemporaryDirectory() as name:
        tmp = Path(name)
        run([sys.executable, CERT / 'cm_all_orders.py', '--save-json', tmp/'all.json', '--csv', tmp/'all.csv'])
        all_polynomials = json.loads((tmp/'all.json').read_text())
        require(all_polynomials == json.loads((CERT/'cm-all-polys.json').read_text()), 'Class polynomials differ')
        same(tmp/'all.csv', CERT/'cm-all-clusters.csv')
        subset = json.loads((CERT/'cm-polys.json').read_text())
        require(all(all_polynomials[k] == v for k,v in subset.items()), 'Residual polynomial differs')
        run([sys.executable, CERT/'cm_extra.py', CERT/'cm-polys.json'], tmp/'residual.csv')
        same(tmp/'residual.csv', CERT/'cm-clusters.csv')
        small_inputs = {line.split()[0] for line in (PRIOR/'cm_small_unresolved.txt').read_text().splitlines()}
        require(small_inputs == set(subset) | {'4075'}, 'Mismatch between residual lists')
        run([sys.executable, PRIOR/'verify_4075.py'])
        run([sys.executable, PRIOR/'verify_four_term.py'])
        for p in (7,13):
            terms = [1,p,p*p,p**3]
            require(all(separate(4*p**6,a,b) for a,b in zip(terms,terms[1:])), 'Split cutoff failed')
        terms = [1,49,169,8281]
        require(all(separate(4*91**4,a,b) for a,b in zip(terms,terms[1:])), 'Conductor cutoff failed')
        compile_program(PRIOR/'cm_small.cpp', tmp/'small')
        run([tmp/'small',10000000], tmp/'raw')
        run([sys.executable, PRIOR/'cm_intervals.py', tmp/'raw'], tmp/'residual')
        same(tmp/'residual', PRIOR/'cm_small_unresolved.txt')
        compile_program(PRIOR/'cm_range.cpp', tmp/'range')
        run([tmp/'range'], tmp/'range.out')
        same(tmp/'range.out', PRIOR/'cm_range.out')
        five = ROOT / 'five'
        cutoff = 4*2401**2
        for terms in ((1,7,49,343,2401), (1,13,49,169,2197), (1,19,49,169,361),
                      (1,31,49,169,361), (1,49,169,361,961)):
            require(4*max(terms)**2 <= cutoff, 'Leading coefficient exceeds range')
            require(all(separate(cutoff,a,b) for a,b in zip(terms,terms[1:])), 'Five-term separation failed')
        compile_program(five/'five_sieve.cpp', tmp/'five-sieve')
        run([tmp/'five-sieve'], tmp/'five-residual', tmp/'five-counts')
        same(tmp/'five-residual', five/'residual.txt')
        same(tmp/'five-counts', five/'counts.txt')
        run([sys.executable, CERT/'cm_extended.py', '--csv', tmp/'extended.csv', '--recompute'],
            tmp/'extended.out', settings={'CM_INTERVAL_BITS':'1800'})
        same(tmp/'extended.out', RECORDED/'cm_extended.out')
        same(tmp/'extended.csv', CERT/'cm-extended-clusters.csv')
        sys.path.insert(0, str(CERT))
        from cm_all_orders import strict_ball_count, translated_polynomial, valuation
        from cm_gen import class_polynomial
        extended = json.loads((CERT/'cm-extended-polys.json').read_text())
        for D,p,r in [(87,19,7), (348,19,7), (432,11,1), (675,11,1)]:
            shifted = translated_polynomial(extended[str(D)],p,0,r)
            require([valuation(c,p) for c in shifted] == [4,3,2,1,0,0,0], 'Sextic valuations differ')
        poly4075 = class_polynomial(4075)
        require(strict_ball_count(translated_polynomial(poly4075,7,0,6),7,Fraction(1,2)) == 6,
                'Six-root witness failed at -4075')
        width_source = CERT/'cm131_width.cpp'
        coefficient_block = width_source.read_text().split('coefficients = {',1)[1].split('};',1)[0]
        width_polynomial = [int(n) for n in re.findall(r'"(-?[0-9]+)"',coefficient_block)] + [1]
        require(width_polynomial == all_polynomials['131'], 'Width checker uses a different polynomial')
        compile_program(width_source, tmp/'width')
        # The large run also uses the proved 17-adic necessary condition.
        for args, record in [([2048], 'cm131_width.out'), ([32768,'--local'], 'cm131_width32768.out')]:
            run([tmp/'width', *args], tmp/record)
            same(tmp/record, RECORDED/record)
        run([sys.executable, CERT/'cm_outlier_width.py', '--width',65536], tmp/'outlier-width.out')
        same(tmp/'outlier-width.out', RECORDED/'cm_outlier_width65536.out')
        run([sys.executable, CERT/'cm_disk_limit.py'], tmp/'disk-limit.out')
        same(tmp/'disk-limit.out', RECORDED/'cm_disk_limit.out')
        print('All exact certificates and finite range computations passed.', flush=True)
if __name__ == '__main__':
    main()
