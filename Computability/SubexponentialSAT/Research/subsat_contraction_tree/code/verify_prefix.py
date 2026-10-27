#!/usr/bin/env python3
"""Deterministic exact checks of the streamed Cauchy prefix kernel.

Optionally pass --original /path/to/the/reviewed/joint_cauchy.py to compare
with the unchanged Fraction-based implementation from the pinned archive.
No downloaded code is fetched or run automatically.
"""
from __future__ import annotations
import argparse, importlib.util, json, random, sys
from pathlib import Path
sys.dont_write_bytecode = True
from cauchy_prefix import PrefixKernel, QuadraticRing, collect

def require(condition, label):
    if not condition:
        raise RuntimeError(label)

def load_original(path):
    spec = importlib.util.spec_from_file_location('reviewed_joint_cauchy', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module

def run(original=None):
    stats = {'modular_feature_cases':0, 'modular_feature_values':0,
             'reconstructed_entries':0, 'fraction_feature_values':0,
             'zero_prefactor_cases':0, 'invalid_inputs_rejected':0}
    rng = random.Random(20310729)
    parameters = []
    for a in range(1,7):
        L = 1 << a
        for i in range(a):
            for sign in (-1,1):
                zeta = ((0,1),(1,1),(-2,3),(4,-4),(0,0))[rng.randrange(5)]
                parameters.append((a,i,sign*(1<<i),rng.choice((1,2,5,13,32,73)),zeta))
    parameters += [(a,i,1<<i,p,(0,1)) for a in (2,3,4) for i in range(a) for p in (2,16,64)]
    for a,i,t,p,zeta in parameters:
        N = 1 << (a-1)
        ports = list(range(N)) if N <= 8 else sorted({0,1,N//3,N//2,N-1})
        fast = PrefixKernel(a,i,t,p,zeta)
        direct = PrefixKernel(a,i,t,p,zeta)
        f = collect(fast,ports,N,'prefix',False)
        d = collect(direct,ports,N,'direct',False)
        require(f == d, 'prefix/direct feature mismatch')
        stats['modular_feature_cases'] += 1
        stats['modular_feature_values'] += len(ports)*N*2
        truncated = collect(PrefixKernel(a,i,t,p,zeta),ports,N,'prefix',True)
        lookup = dict(zip(ports,truncated))
        for j in ports:
            for k in ports:
                value = (0,0)
                ring = QuadraticRing(p)
                for br, (b, target, _) in enumerate(lookup[j]):
                    source = lookup[k][br][2]
                    term = ring.mul(target,source)
                    value = ((value[0]+term[0]) & ring.mask,
                             (value[1]+term[1]) & ring.mask)
                require(value == fast.entry(j,k), 'reconstruction mismatch')
                stats['reconstructed_entries'] += 1
        if zeta == (0,0):
            require(fast.prefactor() == (0,0), 'zero prefactor mishandled')
            stats['zero_prefactor_cases'] += 1
        if original is not None and a <= 4:
            old = original.JointCauchyKernel(a,i,t,original.Quadratic(*zeta))
            target, source = old.feature_tables()
            for j, column in zip(ports,f):
                for b, new_t, new_s in column:
                    require(original.residue(target[b][j],p) == new_t,
                            'Fraction target mismatch')
                    require(original.residue(source[b][j],p) == new_s,
                            'Fraction source mismatch')
                    stats['fraction_feature_values'] += 2
    for args in ((0,0,1,16),(2,2,4,16),(2,0,0,16),(2,0,2,16),(2,0,1,0)):
        try: PrefixKernel(*args)
        except ValueError: stats['invalid_inputs_rejected'] += 1
        else: raise RuntimeError('invalid input accepted')
    # Deliberately remove one power of two from a target. The checker must
    # reject the resulting sum, showing sensitivity to valuation mistakes.
    kernel = PrefixKernel(4,1,2,64)
    cols = collect(kernel,[7],8,'prefix',False)[0]
    ring = kernel.ring
    correct = kernel.entry(7,7)
    altered = (0,0)
    changed = False
    for b,t,s in cols:
        if not changed and any(t) and all(x%2 == 0 for x in t):
            t = (t[0]//2,t[1]//2); changed = True
        term = ring.mul(t,s)
        altered = ((altered[0]+term[0]) & ring.mask,
                   (altered[1]+term[1]) & ring.mask)
    require(changed and altered != correct,'negative valuation control failed')
    stats['negative_control_detected'] = True
    stats['seed'] = 20310729
    stats['status'] = 'passed'
    return stats

if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--original',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=run(load_original(args.original) if args.original else None)
    text=json.dumps(result,indent=2,sort_keys=True)
    if args.output: args.output.write_text(text+'\n')
    print(text)
