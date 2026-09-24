#!/usr/bin/env python3
"""Sparse checks of the q5 packed-bound false-code family.

The proof constructs a fixed inconsistent circuit and extends the aliases
to positive Pell witnesses. These finite checks concern the actual sample
compiler's false assignment and do not instantiate the huge full system.
"""
from collections import defaultdict
from copy import deepcopy
import json
from pathlib import Path

from round37_1980_binary_product_encoding import (
    make_layout, symbolic_checks, assignment, raw_low,
)
from round30_1980_linear_radix_encoding import (
    need, next_power_two, sparse_digits, square_terms,
)


def reordered_layout():
    layout = deepcopy(make_layout())
    names = [name for name,_ in layout['rows']]
    plus,minus = names.index('zero+'),names.index('zero-')
    tp,tm = layout['targets'][plus],layout['targets'][minus]
    gap,M = tm-tp,layout['M']
    need(gap > 12*M, 'two false row bands are disjoint')
    def moved(exponent):
        if tp-4*M-4 <= exponent <= tp: return exponent+gap
        if tm-4*M-4 <= exponent <= tm: return exponent-gap
        return exponent
    D = {moved(p):c for p,c in layout['D'].items()}
    starts = {moved(p):poly for p,poly in layout['starts'].items()}
    need(len(D) == len(layout['D']) and len(starts) == len(layout['starts']),
         'swapping the whole bands causes no collision')
    rows = list(layout['rows'])
    rows[plus],rows[minus] = rows[minus],rows[plus]
    indicator = set(layout['weights'].values())-{0}
    for start in starts: indicator.update(range(start,start+3))
    ecoeff = {p:D.get(p,0)+int(p in indicator) for p in set(D)|indicator}
    layout.update(D=D,starts=starts,rows=rows,indicator=indicator,e_coeff=ecoeff)
    return layout


def check_overflow_lemma():
    count = 0
    for bits in range(3,9):
        n = 1 << bits
        for S in range(1,min(n,40)):
            for t in range(min(n,40)):
                if S&t: continue
                for overflow in range(1,min(n,24)):
                    if S&overflow: continue
                    r = S*(n*n-n)+(overflow*n+t+1)*(n*n-1)
                    expected = (overflow*n**3+(S+t)*n*n
                                +(n-S-overflow-1)*n+n-t-1)
                    need(S+t<n and S+overflow<n and r == expected,
                         'exact valid base-n overflow decomposition')
                    need(r.bit_count() == 2*bits, 'exact central-binomial valuation')
                    count += 1
    return count


def verify():
    layout = reordered_layout()
    structure = symbolic_checks(layout)
    names = [name for name,_ in layout['rows']]
    negative = layout['targets'][names.index('zero-')]
    positive = layout['targets'][names.index('zero+')]
    minimum = layout['weights']['delta']
    K,M = layout['K'],layout['M']
    E = K-8
    low,high = negative-minimum,positive-minimum
    need(minimum == 8 and M<low<high<E-1, 'positive sparse v0 and disjoint support')
    need(max(layout['D']) == E+1 and layout['D'][E+1] == 1,
         'D leads one radix place above the CRT adjustment')
    need(E+minimum == K, 'high adjustment affects no tested coefficient')
    L = next_power_two(3*K+3)
    logical = dict(x=1,delta=1,V0=1,V1=1,X=1,Y=1,Z=1,dc=1,
                   u=0,v=1,a=2,z=3,zero=1)
    records = []
    for H0 in (64,256,1024):
        values = assignment(layout,logical,H0)
        cminus = defaultdict(int)
        for degree,(left,right),multiplicity in square_terms(layout['weights']):
            cminus[degree] += multiplicity*values[left]*values[right]
        cminus[0] -= 1
        cminus = {p:c for p,c in cminus.items() if c}
        need(min(cminus) == 8 and cminus[8] == 2,
             'full canonical C has the required leading C-squared-minus-one term')
        need(all(p%8 == 0 and c>0 for p,c in cminus.items()),
             'other full-C terms are positive and in the same residue class')
        raw = raw_low(layout,values)
        need(raw[negative] == -2 and raw[positive] == 2, 'exact two false rows')
        modified = defaultdict(int,raw)
        for exponent,sign in ((high,1),(low,-1)):
            for degree,coefficient in cminus.items():
                if exponent+degree < K:
                    modified[exponent+degree] -= sign*coefficient
        modified = {p:c for p,c in modified.items() if c}
        for target,(name,_) in zip(layout['targets'],layout['rows']):
            expected = 1 if name.startswith('unit_') else 0
            need(modified.get(target,0) == expected, 'every modified main target is true')
        for start in layout['starts']:
            expected = 1 if start in layout['targets'][-2:] else 0
            need(modified.get(start,0) == expected, 'every extra/helper target remains true')
            need(modified.get(start-4,0) == raw.get(start-4,0) >= 1,
                 'all positive carry resets are unchanged')
        bound = max(sum(map(abs,raw.values())),sum(map(abs,modified.values())))
        B = next_power_two(max(256*bound+1,4*H0,H0+3))
        theta,b = B-2,B-H0-1
        positions = set(layout['indicator']) | {
            start+offset for start in layout['starts'] for offset in range(-6,3)}
        old_digits,_,_ = sparse_digits(raw,positions,B)
        digits,events,_ = sparse_digits(modified,positions,B)
        need(any(old_digits[positive+i]['digit']>1 for i in range(3)) and
             any(old_digits[negative+i]['digit']>1 for i in range(3)),
             'both false windows originally fail')
        need(all(digits[p]['digit'] <= 1 for p in layout['indicator']),
             'every modified third-mask indicator digit passes')
        modulus = B//2-1
        residue = (pow(B,high,modulus)-pow(B,low,modulus))%modulus
        adjustment = (-residue*pow(pow(B,E,modulus),-1,modulus))%modulus
        need((residue+adjustment*pow(B,E,modulus))%modulus == 0,
             'R divides the exact positive v')
        v_mod_theta = (pow(B,high,theta)-pow(B,low,theta)
                       +adjustment*pow(B,E,theta))%theta
        need(v_mod_theta*pow(B,2*L,theta)%theta == 0,
             'the exact fixed-code congruence increment is divisible by theta')
        # v<(B/2+1)B^E while D>(B-2)/(B-1) B^(E+1).
        need(adjustment<B//2 and (B//2+1)*(B-1)<B*(B-2),
             'the leading-digit inequalities prove 0<v<D')
        need(low>M+1 and E+3<K+1<L,
             'theta*v is disjoint from g and below the first q boundary')
        need(max(layout['weights'].values())<L and L+low>K,
             'the first-mask subtraction begins above every nonzero g digit')
        records.append(dict(H0=H0,B=B,crt_coefficient=adjustment,
                            all_indicator_digits_pass=True,
                            repaired_positive=[digits[positive+i]['digit'] for i in range(3)],
                            repaired_negative=[digits[negative+i]['digit'] for i in range(3)],
                            sparse_events=events))
    return dict(status='PASS',structure=structure,cases=records,
                abstract_overflow_cases=check_overflow_lemma(),
                scope='Exact sparse sample-code cancellation, congruence and overflow-lemma checks. The general inconsistent-circuit and full positive Pell extension are in the proof note; no giant full-system witness is instantiated.',
                proof='../1980/EXPLORATION_PACKED_BOUND_Q5_COUNTEREXAMPLE.md')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],len(result['cases']),'sparse q5 aliases;',
          result['abstract_overflow_cases'],'exact overflow cases',flush=True)
