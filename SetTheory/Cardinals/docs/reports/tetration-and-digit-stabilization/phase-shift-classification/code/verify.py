"""Reproduce all finite checks and write CSV certificates and a JSON summary.

Run from any directory: python verify.py --max-base 100000
These checks supplement the written proof; they do not prove a universal claim.
"""
import argparse
import csv
import json
import platform
import sys
import random
import time
from pathlib import Path
from functools import lru_cache
from phase_tetration import (Tower, PhaseModel, vp, split_smooth, word_number,
                            modular_word, sharp_onset_base)

TARGET = {2,4,5,6,8,9,19,28,46,64,82,2486,2684,3971,4268,4862,6248,
          6842,7931,8426,8624}
EVEN_TARGET = {2,4,6,8,28,46,64,82,2486,4268,4862,6248,6842,8426}
MODULAR_TARGET = (TARGET - {19,3971,7931}) | {
    19,91,1397,1793,3179,3971,7139,7931,9317,9713}
# Accessed 2026-09-19, OEIS A376842 revision #39 (2026-03-30).
OEIS = [8,46,6248,5,4268,2684,6842,2,-1,4,46,6248,8,5,64,4,28,4862,-1,
        6248,6248,2486,8,5,46,2684,4862,6842,-1,8426,8426,28,28,5,4,
        2684,28,82,-1,64,4268,46,4268,5,4862,4,2,6842,-1,5,6,8,6248,
        5,8426,2684,4268,2]


def euler_residue(a, h, m):
    """Second algorithm: full-modulus Euler reduction with exponent lifting.

    Unlike Tower.mod, this does not split the result into prime-power
    residues or combine it by CRT.  It shares only the capped-tower helper.
    """
    tower = Tower(a)
    @lru_cache(None)
    def rec(h, m):
        if m == 1:
            return 0
        if h == 0:
            return 1 % m
        e2, e5 = split_smooth(m)
        phi = ((2 ** (e2-1)) if e2 else 1) * (
            (4 * 5 ** (e5-1)) if e5 else 1)
        cap = tower.capped(h-1, phi)
        exponent = cap if cap < phi else rec(h-1, phi) + phi
        return pow(a, exponent, m)
    return rec(h,m)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-base', type=int, default=100000)
    parser.add_argument('--random-cases', type=int, default=100)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parent.parent / 'data')
    args = parser.parse_args()
    if args.max_base < 901 or args.random_cases < 0:
        parser.error('max-base must be at least 901; random-cases nonnegative')
    args.output.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    witnesses, even_witnesses = {}, {}
    mismatches = []
    checked_bases = checked_phases = 0
    distribution = {str(x):0 for x in sorted(TARGET)}
    for a in range(2, args.max_base + 1):
        if a % 10 == 0:
            continue
        model = PhaseModel(a)
        B = model.onset()
        w = model.phase_word()
        assert w == model.predicted_word(), ('model mismatch',a)
        number = word_number(w)
        assert number in TARGET, ('unlisted word',a,number)
        witnesses.setdefault(number,a)
        distribution[str(number)] += 1
        if a % 2 == 0:
            assert number in EVEN_TARGET, ('even restriction',a,number)
            even_witnesses.setdefault(number,a)
        for b in range(B, B+8):
            k = model.k(b)
            assert k-model.k(b-1) == model.speed, ('speed',a,b)
            s = model.tower.decimal_phase(b,k)
            assert s == w[(b-B) % len(w)], ('period',a,b)
            checked_phases += 1
        if B > 1:
            assert model.k(B-1)-model.k(B-2) != model.speed, ('minimality',a)
        if a < 60 and OEIS[a-2] != number:
            mismatches.append({'base':a,'listed':OEIS[a-2],'calculated':number})
        checked_bases += 1
        if a % 10000 == 9999:
            print(f'Checked through base {a} ({time.perf_counter()-start:.1f}s)', file=sys.stderr, flush=True)
    assert set(witnesses) == TARGET
    assert set(even_witnesses) == EVEN_TARGET
    assert mismatches == [{'base':21,'listed':6248,'calculated':2486}]

    print('Starting direct checks', file=sys.stderr, flush=True)
    # Direct integer towers: independent of either modular algorithm.
    direct_cases = 0
    for a in range(2,81):
        exact = [1,a,a**a]
        if a <= 6:
            exact.append(a ** exact[-1])
        if a == 2:
            exact.append(2 ** exact[-1])  # T_4=65536
            exact.append(2 ** exact[-1])  # T_5 has 65537 binary digits
        tower = Tower(a)
        for h,n in enumerate(exact):
            for e2,e5 in ((0,1),(1,0),(4,7),(7,4),(10,10),(15,3)):
                m=2**e2*5**e5
                assert tower.mod(h,m)==n%m, ('direct residue',a,h,m)
                direct_cases += 1
            for cap in (1,2,3,7,101,10000):
                assert tower.capped(h,cap)==min(n,cap), ('direct cap',a,h,cap)
                direct_cases += 1
        if a%10:
            model=PhaseModel(a)
            for b in range(1,len(exact)-1):
                d=exact[b+1]-exact[b]
                assert model.k(b)==min(vp(d,2),vp(d,5)), ('direct valuation',a,b)
                direct_cases += 1

    print('Starting independent Euler checks', file=sys.stderr, flush=True)
    rng=random.Random(376842)
    random_checks=0
    for _ in range(args.random_cases):
        a=rng.randrange(2,10**rng.randrange(2,42))
        h=rng.randrange(0,25)
        digits=rng.randrange(1,61)
        m=10**digits
        assert Tower(a).mod(h,m)==euler_residue(a,h,m), ('Euler check',a,h,digits)
        random_checks += 1

    # Parametric worst-case onset examples. The largest has onset 34.
    structured=[]
    for r in (3,5,8,12,16,24,32):
        print(f'Structured r={r} ({time.perf_counter()-start:.1f}s)', file=sys.stderr, flush=True)
        a=sharp_onset_base(r)
        model=PhaseModel(a)
        assert model.t==r-1 and model.r==r and model.onset()==r+2
        B=model.onset()
        assert model.valuations_capped(B-1)[0]==model.valuations_capped(B-1)[1]
        w=model.phase_word()
        assert w==(5,)
        # One high-precision independent residue check per constructed base.
        digits=model.k(B)+1
        modulus=10**digits
        assert model.tower.mod(B,modulus)==euler_residue(a,B,modulus)
        structured.append({'r':r,'base':str(a),'onset':B,'speed':r-1,
                           'k_at_onset':model.k(B),'aps':5})

    print('Starting modular-anchor witnesses', file=sys.stderr, flush=True)
    # Balanced towers and all rotations for A376446.
    mod_witnesses={}
    for a in list(range(2,1000)) + [1+c*10**v for c in (1,3,7,9) for v in range(2,8)]:
        if a%10==0:
            continue
        n=word_number(modular_word(a))
        assert n in MODULAR_TARGET, ('modular range',a,n)
        mod_witnesses.setdefault(n,a)
    assert set(mod_witnesses)==MODULAR_TARGET

    with (args.output/'witnesses.csv').open('w',newline='') as f:
        cols=['aps','base','onset','speed','k_at_onset','first_phase',
              'modulus','T_B_mod','T_Bplus1_mod','even_witness']
        writer=csv.DictWriter(f,fieldnames=cols); writer.writeheader()
        for word,a in sorted(witnesses.items()):
            model=PhaseModel(a); B=model.onset(); k=model.k(B); m=10**(k+1)
            writer.writerow(dict(aps=word,base=a,onset=B,speed=model.speed,
                k_at_onset=k,first_phase=model.phase_word()[0],modulus=m,
                T_B_mod=model.tower.mod(B,m),T_Bplus1_mod=model.tower.mod(B+1,m),
                even_witness=even_witnesses.get(word,'')))
    for name, rows in [('sharp_onsets.csv',structured),
                       ('modular_witnesses.csv',[{'word':w,'base':a}
                         for w,a in sorted(mod_witnesses.items())])]:
        with (args.output/name).open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)
    summary=dict(date='2026-09-19',python=platform.python_version(),
        max_base=args.max_base,bases_checked=checked_bases,phase_positions_checked=checked_phases,
        direct_integer_checks=direct_cases,independent_Euler_checks=random_checks+len(structured),
        sharp_onset_examples=len(structured),largest_structured_onset=34,
        aps_values=sorted(witnesses),even_aps_values=sorted(even_witnesses),
        modular_values=sorted(mod_witnesses),published_data_discrepancies=mismatches,
        observed_distribution=distribution,seconds=round(time.perf_counter()-start,3),
        status='All mathematical assertions in this test run passed. The documented OEIS discrepancy remains.')
    (args.output/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
