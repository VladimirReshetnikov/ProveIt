#!/usr/bin/env python3
"""Finite interior upper-bit padding exploration for the A1031 layout."""
import argparse
import hashlib
import importlib.util
import json
from math import gcd, lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'research/start-marker-independent/certify.py'
PARENT_SHA = '569d9da678dea56d1b610b2e1c436686e361b19ec66ad6cd2683c59344441067'
RHO, M = 1 << 47, 1 << 44
A, C1, C2 = 1031, 2042, 3074
FIRST, LAST, COUNT, LOW_BITS = 3981, 4105, 125, 40


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    require(sha(PARENT.read_bytes()) == PARENT_SHA, 'Frozen complete4177 finite source')
    spec = importlib.util.spec_from_file_location('padding_parent', PARENT)
    require(spec is not None and spec.loader is not None, 'Import specification')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    helper, seed, actions, tiles, c, _ = module.model()
    layout = {key: value for key, value in module.SPEC.items() if key not in {'padding', 'zero_end'}}
    layout.update(anchor=A, centers=[C1, C2])
    support = {e for e, v in enumerate(c) if v} | {990, 991, A}
    require(len(support) == 980 and c[A] == c[990] == c[991] == 0,
            'Complete new physical support and zero weights')
    dc = module.dc_coefficients(c, layout)
    require(max(dc) + max(support) == LAST and LAST - FIRST + 1 == COUNT,
            'Entire125-field rectangle ends at maximum product')
    require(FIRST > A + 10 and FIRST > C2, 'No temporal/spatial/core-mask contribution in rectangle')
    inputs = [(-1, [])]
    for index, (w, n, e, s) in enumerate(tiles):
        bits = [index]
        for value, base in zip((255-w, 511-n, 255-e, 511-s), (992, 973, 1002, 943)):
            bits.extend(base+j for j in range(value.bit_length()) if value >> j & 1)
        require(len(set(bits)) == len(bits) and set(bits) <= support, 'Every decoded word uses full physical support')
        inputs.append((index, bits))
    require(len(inputs) == 944, 'All943 tiles plus empty cell, including forbidden selector conservatively')
    rows = []
    for target in range(FIRST, LAST+1):
        values = [(sum(dc.get(target-e, 0) for e in bits), index) for index, bits in inputs]
        maximum, witness = max(values)
        # Nonnegative weights make these exact maxima over independent marker/dummies.
        extras = dc.get(target-A, 0) + 3*dc.get(target-990, 0) + dc.get(target-991, 0)
        bound = maximum + extras + 29
        require(bound < 1 << LOW_BITS, 'Every decoded raw value plus arbitrary incoming carry stays below2^40')
        rows.append({'field': target, 'tile_maximum': maximum, 'maximizing_tile': witness,
                     'marker_and_dummy_maximum': extras, 'with_carry29': bound})
    require(max(row['with_carry29'] for row in rows) == 761886127172, 'Exact full rectangle bound')
    require(COUNT * (47-LOW_BITS) == 875, 'Whole padding population')
    require(c[0] + 29 < RHO and max(dc) + 990 == 4064, 'Final reset and safe-dummy local exponent')
    power = lambda e: 1 << (47*e)
    padding = (RHO - (1 << LOW_BITS)) * sum(power(e) for e in range(FIRST, LAST+1))
    require(padding.bit_count() == 875, 'Whole875-bit rectangular mask')
    dc_integer = sum(v*power(e) for e, v in dc.items())
    trials = []
    selected = None
    for length in range(LAST+1, LAST+101):
        divisor = helper.least_factor(length)
        trial = {'L': length, 'least_factor': divisor}
        trials.append(trial)
        if divisor is not None or length == 47:
            continue
        d, B = 47*length, power(length)
        beta = B-1
        K = dc_integer + power(length+10)
        MC = beta - sum(power(e) for e in support if e != 1) - 2*power(990)
        native = 4 + (M-2)*(power(C1)+power(C2))
        native += sum(power(e) for e in range(973,982)) + sum(power(e) for e in range(1012,1020)) + power(A)
        native += padding
        whole = {'beta': beta, 'K': K, 'MC': MC, 'MF_source': native+beta}
        require(0 < MC < beta and 0 < native < beta and 0 < dc_integer < B,
                'Whole scalar boxes')
        require(native.bit_count() == 980 and MC.bit_count() == d-980,
                'Whole complementary populations')
        require(MC % 4 == 2 and native % 8 == 4, 'Whole origin residues')
        fixed = []
        for p in (47, length):
            row = module.modular(p, c, tiles, layout, length, whole)
            row['base2_order'], row['B_order'] = helper.order(2,p), helper.order(row['B'],p)
            fixed.append(row)
        trial['fixed'] = fixed
        if any(row['H'] == 0 or row['B_squared'] == 1
               or row['base2_order']['order'] != row['B_order']['order']
               or gcd(d, row['B_order']['order']) != 1 for row in fixed):
            continue
        spacing = lcm(*(row['B_order']['order'] for row in fixed))
        require(gcd(d, spacing) == 1, 'Coprime full controller spacing')
        auxiliary = []
        for j in range((d-1)//spacing+1, (d-1)//spacing+502):
            p = j*spacing+1
            divisor = helper.least_factor(p)
            row = {'candidate': p, 'multiplier': j, 'least_factor': divisor}
            auxiliary.append(row)
            if divisor is not None:
                continue
            row.update(module.modular(p,c,tiles,layout,length,whole))
            lift = pow(2,d*(p-1),p*p)
            require(lift % p == 1, 'Fermat lift')
            row['lift_residue'], row['lift_quotient'] = lift, (lift-1)//p
            if row['H'] and row['B_squared'] != 1 and row['lift_quotient']:
                require(p > d and p % 2 == 1, 'Odd auxiliary prime above d')
                selected = {'L':length, 'd':d, 'fixed':fixed, 'spacing':spacing,
                            'auxiliary_trials':auxiliary, 'lambda':p}
                break
        if selected:
            break
    require(selected is not None and selected['L'] == 4111 and selected['d'] == 193217,
            'Exact selected whole length')
    require([row['base2_order']['order'] for row in selected['fixed']] == [23,2055]
            and selected['spacing'] == 47265 and selected['lambda'] == 567181,
            'Exact new complete controller')
    require(selected['L'] - (LAST+1) == 5 and all(selected['L']-(e+1) >= 3 for e in (4064,1000,990)),
            'Five zero top fields and complete ordinary safe-dummy margins')
    ports = {}
    for key, value in whole.items():
        raw = value.to_bytes((value.bit_length()+7)//8, 'big')
        ports[key] = {'bits':value.bit_length(), 'bytes':len(raw), 'sha256':sha(raw)}
    raw_bytes = sum(row['bytes'] for row in ports.values())
    require(raw_bytes == 96670, 'Exact whole four-port byte cost')
    data = {'schema':'start_marker1031_rectangular_padding_exploration_v1',
            'script_sha256':sha(Path(__file__).read_bytes()), 'parent_verifier_sha256':PARENT_SHA,
            'seed_sha256':sha(seed.encode()), 'actions_sha256':sha(encoded(actions)),
            'tiles_sha256':sha(encoded(tiles)), 'full3297_coefficients_sha256':sha(encoded(c)),
            'layout':layout, 'padding':{'first':FIRST,'last':LAST,'count':COUNT,'zero_bits':[40,46],
            'population':875,'maximum_with_carry29':max(row['with_carry29'] for row in rows),'rows':rows},
            'length_trials':trials, 'controller':selected, 'constant_ports':ports, 'raw_bytes':raw_bytes,
            'scope':'Complete finite upper-bit rectangle and whole new tuple/controller. Relies on separately proved A1031 decoding/alignment/carry29. No complete new ordinary proof or page promotion is claimed.'}
    raw = encoded(data)
    target = HERE/'RESULTS.json'
    if args.write:
        target.write_bytes(raw)
    else:
        require(target.read_bytes() == raw, 'Deterministic receipt differs')
    print(json.dumps({'status':'PASS','raw_bytes':raw_bytes,'L':4111,'lambda':567181,
                      'receipt_sha256':sha(raw),'script_sha256':data['script_sha256']},sort_keys=True))


if __name__ == '__main__':
    main()
