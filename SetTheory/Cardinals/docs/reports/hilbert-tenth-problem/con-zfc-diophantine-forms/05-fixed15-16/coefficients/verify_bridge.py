"""Reproducible finite checks of the machine/window/coefficient interfaces."""
from itertools import product
from pathlib import Path
from types import SimpleNamespace
import json
import random
from fixed_machine import Machine, count_windows, local_valid, tile_alphabet, verify, require
from coefficient_recipe import specification, materialize_for_windows

HERE = Path(__file__).resolve().parent


def crosscheck_counter():
    rng = random.Random(20261022)
    checks = []
    for case in range(4):
        states, symbols = (0,1), (0,1)
        table = {(q,a):(rng.choice(states),rng.choice(symbols),rng.choice((-1,0,1)))
                 for q,a in product(states,symbols)}
        for a in symbols:
            table[1,a] = (1,a,0)
        m = SimpleNamespace(states=states,alphabet=symbols,start=0,halt=1,blank=0,
                            delta=lambda q,a,table=table: table[q,a])
        alphabet = tile_alphabet(m)
        crosses = 0
        for d,l,c,r,u in product(alphabet,repeat=5):
            w = (alphabet[0],d,alphabet[0],l,c,r,alphabet[0],u,alphabet[0])
            crosses += local_valid(w,m)
        count,fast = count_windows(m)
        require(crosses == fast and count == crosses*len(alphabet)**4, 'factored count vs direct enumeration')
        checks.append(dict(case=case,tile_count=len(alphabet),crosses=crosses,
                           tested_crosses=len(alphabet)**5))
    return checks


def verify_coefficient_bounds():
    s = specification()
    g = s['geometry']
    require(g['b'] == g['L'] == 5**45 and g['d'] == 5**90, 'explicit fixed powers')
    require(g['A'] == 2**100 and g['dummy_count'] == 1, 'actual compiler choice')
    require(g['m'] == 2*(g['ell']-1+g['J'])+12*g['a']+2, 'exact population formula')
    require(g['K'] == g['k']+9*g['a']+5, 'one-dummy cardinality')
    require(g['dummy0']+1 < g['E'], 'extra dummy spill support')
    require(g['T2']-g['T1'] > 2*g['E'], 'duplicated center band separation')
    require(g['L']-(g['T2']-g['T1']) > g['E'], 'cyclic gap separation')
    require(g['L'] > g['g']+g['E'], 'whole field degree bound')
    require(g['b'] >= g['ell']*(g['J']+2)+g['guard'].bit_length(), 'large radix proof premise')
    # 4(K+2)(2*S+6)+8 <= 112(K+2)n*A^J+24(K+2)+8,
    # while guard*A^J dominates that expression already for A^J>=1.
    n = g['k']+9*g['a']+4
    require(g['guard'] >= 112*(g['K']+2)*n+24*(g['K']+2)+8, 'scaled mass bound')
    require(g['guard'] >= 16 and g['A'] >= 16 and g['J'] >= 1, 'mu and minimum radix bounds')
    return dict(A=g['A'],b_power5=45,L_power5=45,d_power5=90,
                masks_expanded=False,
                established='all numerical premises of the symbolic radix, separation, population and five-adic arguments')


def verify_toy_materialization():
    # This fully expands one small independent compiler input. It exercises
    # the literal materializer and its exact mask bit-population/range tests.
    result = materialize_for_windows(((0,)*9,(1,)*9),2)
    return dict(window_count=2,tile_alphabet=2,
                b=result['geometry']['b'],d=result['geometry']['d'],
                B_bit_length=(result['Bm1']+1).bit_length(),
                high_correction=result['high_correction'],
                witness_input='two distinct constant windows; not a universal machine')


if __name__ == '__main__':
    receipt = dict(machine=verify(),cross_counter=crosscheck_counter(),
                   coefficient_bounds=verify_coefficient_bounds(),
                   toy_coefficients=verify_toy_materialization())
    (HERE/'bridge_verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS: 430 table-isomorphism rows, 3440 folded cases, 32 preludes, '
          '995328 direct cross predicates, exact compiler bounds, one materialized toy compiler.')
